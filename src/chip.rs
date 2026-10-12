use crate::{
    cmd::{CC_CONTEXT_LOAD, CC_CONTEXT_SAVE, CC_FLUSH_CONTEXT},
    module::{ContextIo, IoErr},
    msg::{ST_NO_SESSIONS, build_header},
    rewrite::{HEADER_SIZE, read_be32},
};

pub const RC_SUCCESS: u32 = 0x0000_0000;
/// 位 7 置位表示「格式一」返回码：低 6 位是错误号，位 8..11 是出错的
/// 句柄 / 参数 / 会话序号。分类时必须先把序号位抹掉。
const RC_FMT1_BIT: u32 = 0x0000_0080;
/// TPM Format-1 返回码中的 selector bits：
/// - bit 6 (`TPM_RC_P`) 表示参数选择器；
/// - bits 8..11 (`TPM_RC_N`) 表示对象 / 会话编号；
///   这两部分必须在分类前清掉，否则 `TPM_RC_HANDLE | P | N` 会被误判成
///   另一个错误码。
const RC_FMT1_MASK: u32 = 0x0000_00BF;
const RC_HANDLE: u32 = 0x0000_008B;
const RC_INTEGRITY: u32 = 0x0000_009F;
const RC_CONTEXT_GAP: u32 = 0x0000_0901;
const RC_OBJECT_MEMORY: u32 = 0x0000_0902;
const RC_SESSION_MEMORY: u32 = 0x0000_0903;
const RC_MEMORY: u32 = 0x0000_0904;
const RC_REFERENCE_H0: u32 = 0x0000_0910;
pub const RC_YIELDED: u32 = 0x0000_0908;
pub const RC_TESTING: u32 = 0x0000_090A;
pub const RC_RETRY: u32 = 0x0000_0922;
fn rc_value(rc: u32) -> u32 {
    if rc & RC_FMT1_BIT == RC_FMT1_BIT {
        rc & RC_FMT1_MASK
    } else {
        rc
    }
}
/// 返回码 → 编排层错误。
///
/// 分类的语义边界只有一条要紧：什么算 [`IoErr::NotFound`]。它表示「目标
/// 已不存在」，编排层据此把对应槽位直接遗忘而不是让整条路径失败——所以
/// 这里只能放真正表示「引用了不存在的对象」的两个返回码，放宽会让状态
/// 不一致被静默吞掉。
fn classify_rc(rc: u32) -> IoErr {
    let v = rc_value(rc);
    if v == RC_HANDLE || v == RC_REFERENCE_H0 {
        IoErr::NotFound
    } else if v == RC_INTEGRITY {
        IoErr::Integrity
    } else if v == RC_CONTEXT_GAP
        || v == RC_OBJECT_MEMORY
        || v == RC_SESSION_MEMORY
        || v == RC_MEMORY
    {
        IoErr::NoSpace
    } else if v == RC_RETRY || v == RC_YIELDED || v == RC_TESTING {
        IoErr::Timeout
    } else {
        IoErr::Fatal
    }
}
/// 备份块的定长前缀：序号 8 字节、句柄 4 字节、层级 4 字节、数据长度 2 字节。
const CTX_FIXED: usize = 18;
/// 数据长度字段在备份块内的偏移。
const CTX_SIZE_OFF: usize = 16;
/// 一次完整的命令 / 响应往返。
///
/// 这是本层与芯片之间唯一的接触点。实现方要么把假设直接摆在自己的
/// `external_body` 里，要么像链路层那样把假设收进一个零大小的幽灵账本；
/// 无论哪种，下面写下的后置条件都是本模块**据以推理的全部依据**。它们按命令
/// 码分情况给出，而不是笼统地断言「句柄是新的」——这样每条假设都能指到具体
/// 的规范条款上。
///
/// TRUST 1：响应写入不越过 `rsp` 容量，且至少包含一个完整报文头。
/// 依据：传输层按声明长度收字节，不足即报错。
///
/// TRUST 2：ContextLoad 成功时返回的句柄不在 `live()` 中。
/// 依据：句柄在被显式释放或换出之前唯一标识一个已装载对象，芯片不会把
/// 一个仍然有效的句柄再次分配出去。**这是本模块单射性的最终来源**，
/// 也是整个 TCB 里最实质的一条。
///
/// TRUST 3：`live()` 只随 ContextLoad 成功而增长、随 FlushContext 而收缩，
/// 其余命令不改变它。
///
/// 关于释放命令的那条例外：它**不以传输成功为条件**。传输失败时本端无从得知
/// 芯片是否已经释放，与其两边都不确定，不如统一按「本端不再追踪」处理——芯片
/// 若确实没释放，那份资源会占到复位为止，这是已知且无从补救的泄漏。因此
/// 「失败即无副作用」那条必须把释放命令排除在外，否则两条同时要求
/// `live == old` 与 `live == old.remove(h)`，只有 `h` 本就不在集合里时才能
/// 同时满足，实现方一个也做不出来。
pub trait ChipTransport {
    fn exec(&mut self, cmd: &[u8], rsp: &mut [u8]) -> Result<usize, IoErr>;
}
/// 命令与响应暂存区的容量。上下文数据块可以接近一页，两个缓冲区
/// 内联在结构体里共 8 KiB；若目标平台栈紧张，把它们换成调用方提供的
/// 切片即可，本模块的证明不依赖它们的存储方式。
pub(crate) const MSG_MAX: usize = 4096;
/// 把 [`ChipTransport`] 抬成编排层要的 [`ContextIo`]。
///
/// 这一层是完全验证的：它做的全部事情是长度校验、报文组装、返回码分类。
/// 幽灵集合直接透传给传输层，本层不引入任何新的假设——这一点要靠三个方法
/// 都没有 `external_body` 来保证，一旦有一个被标上，上面那句话就不再成立，
/// 而编排层的单射性正是建立在这句话之上。
pub struct CtxIo<T: ChipTransport> {
    tx: T,
    cbuf: [u8; MSG_MAX],
    rbuf: [u8; MSG_MAX],
}
impl<T: ChipTransport> CtxIo<T> {
    pub fn new(tx: T) -> Self {
        CtxIo {
            tx,
            cbuf: [0u8; MSG_MAX],
            rbuf: [0u8; MSG_MAX],
        }
    }
    /// 把 10 字节报文头落到命令缓冲区开头。
    ///
    /// 后置条件里那句「幽灵集合不变」不是形式主义：组装报文与芯片状态无关，
    /// 把这一点写下来，后面每个方法才能把「进入函数时的集合」一路带到发送
    /// 那一刻，而不必在中途重新为它找依据。
    fn put_header(&mut self, code: u32, total: usize) {
        let hdr = build_header(ST_NO_SESSIONS, code, total as u32);
        self.cbuf[..HEADER_SIZE].copy_from_slice(&hdr);
    }
    /// 把整条命令原样交给底层传输，不做报文组装。
    ///
    /// 与 `ContextIo` 的三个方法共享同一个传输层账本，因此在 `exec_raw`
    /// 与 `load`/`save`/`flush` 之间交替调用时，句柄记账是连续的。
    pub fn exec_raw(&mut self, cmd: &[u8], rsp: &mut [u8]) -> Result<usize, IoErr> {
        self.tx.exec(cmd, rsp)
    }
    /// 交回底层传输，结束上下文往返阶段。
    ///
    /// 取走 `self`，两块暂存区随之释放，幽灵集合原样落到返回值上。后置条件
    /// 里那句相等是阶段移交的依据：适配器代管期间对芯片做过什么，交回去的
    /// 传输层照单全收，不重算也不清零。
    pub fn release(self) -> T {
        self.tx
    }
}
impl<T: ChipTransport> ContextIo for CtxIo<T> {
    fn load(&mut self, blob: &[u8], off: usize) -> Result<(u32, usize), IoErr> {
        if off > blob.len() || blob.len() - off < CTX_FIXED {
            return Err(IoErr::Integrity);
        }
        let size =
            u16::from_be_bytes([blob[off + CTX_SIZE_OFF], blob[off + CTX_SIZE_OFF + 1]]) as usize;
        let used = CTX_FIXED + size;
        if blob.len() - off < used {
            return Err(IoErr::Integrity);
        }
        if MSG_MAX - HEADER_SIZE < used {
            return Err(IoErr::NoSpace);
        }
        self.put_header(CC_CONTEXT_LOAD, HEADER_SIZE + used);
        self.cbuf[HEADER_SIZE..HEADER_SIZE + used].copy_from_slice(&blob[off..off + used]);
        let n = self.tx.exec(&self.cbuf, &mut self.rbuf)?;
        if n < HEADER_SIZE {
            return Err(IoErr::Protocol);
        }
        let rc = read_be32(&self.rbuf, 6);
        if rc != RC_SUCCESS {
            return Err(classify_rc(rc));
        }
        if n < HEADER_SIZE + 4 {
            return Err(IoErr::Protocol);
        }
        let h = read_be32(&self.rbuf, HEADER_SIZE);
        Ok((h, used))
    }
    fn save(&mut self, h: u32, out: &mut [u8], off: usize) -> Result<usize, IoErr> {
        self.put_header(CC_CONTEXT_SAVE, HEADER_SIZE + 4);
        write_be32_arr(&mut self.cbuf, HEADER_SIZE, h);
        let n = self.tx.exec(&self.cbuf, &mut self.rbuf)?;
        if n < HEADER_SIZE {
            return Err(IoErr::Protocol);
        }
        let rc = read_be32(&self.rbuf, 6);
        if rc != RC_SUCCESS {
            return Err(classify_rc(rc));
        }
        let body = n - HEADER_SIZE;
        if body < CTX_FIXED {
            return Err(IoErr::Protocol);
        }
        if off > out.len() || out.len() - off < body {
            return Err(IoErr::NoSpace);
        }
        out[off..off + body].copy_from_slice(&self.rbuf[HEADER_SIZE..HEADER_SIZE + body]);
        Ok(body)
    }
    fn flush(&mut self, h: u32) {
        self.put_header(CC_FLUSH_CONTEXT, HEADER_SIZE + 4);
        write_be32_arr(&mut self.cbuf, HEADER_SIZE, h);
        let _ = self.tx.exec(&self.cbuf, &mut self.rbuf);
    }
}
/// [`write_be32`] 的定长数组版本。切片版要求 `&mut [u8]`，而这里操作的是
/// 结构体里的数组字段，重借用会让 Verus 多出一层义务，直接写更省事。
fn write_be32_arr(b: &mut [u8; MSG_MAX], off: usize, v: u32) {
    b[off..off + 4].copy_from_slice(&v.to_be_bytes());
}
#[cfg(test)]
mod tests {
    use super::*;
    struct FakeChip {
        rsp: [u8; HEADER_SIZE],
    }
    impl ChipTransport for FakeChip {
        fn exec(&mut self, _cmd: &[u8], rsp: &mut [u8]) -> Result<usize, IoErr> {
            let n = self.rsp.len().min(rsp.len());
            for i in 0..n {
                rsp[i] = self.rsp[i];
            }
            Ok(n)
        }
    }
    #[test]
    fn context_load_rc_handle_short_response_is_not_protocol() {
        let mut io = CtxIo::new(FakeChip {
            rsp: {
                let mut arr = [0u8; HEADER_SIZE];
                arr[6] = 0x00;
                arr[7] = 0x00;
                arr[8] = 0x00;
                arr[9] = 0x8B;
                arr
            },
        });
        let blob = [0u8; CTX_FIXED];
        let err = io.load(&blob, 0);
        assert!(matches!(err, Err(IoErr::NotFound)));
    }
}
