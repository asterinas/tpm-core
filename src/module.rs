pub use crate::{
    handle::{
        SLOTS, is_session_exec as is_session, is_transient_exec as is_transient,
        valid_phandle_exec as valid_phandle,
    },
    rewrite::{HeaderOutcome, SpaceErr},
    table::{CtxSlot, SpaceTable},
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IoErr {
    /// 目标已不存在：上下文被外部释放，或计数器不匹配。可恢复——
    /// 对应槽位直接遗忘即可。
    NotFound,
    /// 备份数据完整性校验失败。
    Integrity,
    /// 备份缓冲区放不下。
    NoSpace,
    /// 轮询预算耗尽，纯粹的等待超时，值得按退避策略重试。
    Timeout,
    /// 物理总线故障，重试没有意义。
    Bus,
    /// 芯片返回的东西违反协议约定（长度、状态位与规范不符）。
    Protocol,
    /// 调用方交下来的命令本身不自洽（长度字段与缓冲区对不上）。
    /// 这是编码层的逻辑错误，不是设备故障。
    BadCommand,
    /// 调用时序错误：接口在不满足前提的状态下被调用。
    NotReady,
    /// 表与芯片状态已经无法调和的内部不变量破裂，唯一安全动作是
    /// 整体清空重来。
    Fatal,
}
/// 上下文存取的抽象接口。
///
/// 实现由外层提供：它内部会做报文构造、传输、返回码分类，那些属于编解码
/// 层的职责。本模块只依赖这里写下的前后置条件。
pub trait ContextIo {
    /// 从 `blob[off..]` 装载一份上下文，返回新句柄与消耗的字节数。
    fn load(&mut self, blob: &[u8], off: usize) -> Result<(u32, usize), IoErr>;
    /// 把 `h` 的上下文保存到 `out[off..]`，返回写入字节数。
    ///
    /// 保存本身不释放句柄，释放要显式调用 [`ContextIo::flush`]。
    fn save(&mut self, h: u32, out: &mut [u8], off: usize) -> Result<usize, IoErr>;
    /// 释放芯片上的句柄。幂等，不返回错误——释放失败无从补救，
    /// 且调用点全在错误处理路径上。
    fn flush(&mut self, h: u32);
}
/// 使用者可见的句柄空间。备份缓冲区不放在这里——本层不做分配，
/// 由外层按需提供切片。
pub struct Space {
    tbl: SpaceTable,
}
/// 一次请求期间的工作副本。只有 [`Space::commit`] 会把它写回。
///
/// 没有实现 `Clone`，也没有公开构造函数：拿到它的唯一途径是
/// [`Space::begin`]，丢弃它的唯一后果就是回滚。
pub struct Transaction {
    work: SpaceTable,
}
impl Space {
    pub fn new() -> Self {
        Space {
            tbl: SpaceTable::new(),
        }
    }
}

impl Default for Space {
    fn default() -> Self {
        Self::new()
    }
}

impl Space {
    /// 取一份工作副本。使用者可见的状态在此期间保持不变。
    pub fn begin(&self) -> Transaction {
        Transaction { work: self.tbl }
    }
    /// 把工作副本写回。只在整条路径都成功时调用。
    pub fn commit(&mut self, t: Transaction) {
        self.tbl = t.work;
    }
}
impl Transaction {
    pub fn table(&mut self) -> &mut SpaceTable {
        &mut self.work
    }
    /// 事务失败时的收尾：释放芯片上的残留，然后丢弃副本。
    ///
    /// 取走 `self` 而不是借用——收尾之后这个事务不可能再被提交。
    pub fn abort<I: ContextIo>(self, io: &mut I) {
        let mut t = self;
        flush_all(&mut t.work, io);
    }
}
/// 释放表中所有活跃句柄与所有会话，并清空两张表。
///
/// 这是错误路径的收尾动作：调用之后芯片上不再残留本 space 的任何东西。
fn flush_all<I: ContextIo>(tbl: &mut SpaceTable, io: &mut I) {
    for i in 0..SLOTS {
        if let CtxSlot::Live(h) = tbl.slot_at(i) {
            io.flush(h);
        }
        tbl.set_slot_free(i, false);
    }
    for i in 0..SLOTS {
        let h = tbl.session_at(i);
        if h != 0 {
            io.flush(h);
            tbl.clear_session(i);
        }
    }
}
/// 把备份缓冲区里的上下文全部装载回芯片。
///
/// 成功返回后表中不再有「已保存」状态的槽位——每个非空槽位都对应一个
/// 芯片上真实存在的句柄。
///
/// 会话的处理与对象不同：装载失败的会话被直接遗忘（清空槽位）而不是
/// 让整个操作失败。会话本来就可能被外部释放，这是正常情形。
pub fn load_space<I: ContextIo>(
    tbl: &mut SpaceTable,
    io: &mut I,
    ctx_buf: &[u8],
    ses_buf: &[u8],
) -> Result<(), IoErr> {
    let mut off: usize = 0;
    for i in 0..SLOTS {
        match tbl.slot_at(i) {
            CtxSlot::Empty => {}
            CtxSlot::Live(_) => {
                flush_all(tbl, io);
                return Err(IoErr::NotReady);
            }
            CtxSlot::Saved => match io.load(ctx_buf, off) {
                Ok((h, used)) => {
                    tbl.set_slot_live(i, h);
                    off += used;
                }
                Err(e) => {
                    flush_all(tbl, io);
                    return Err(e);
                }
            },
        }
    }
    let mut off: usize = 0;
    for i in 0..SLOTS {
        if tbl.session_at(i) != 0 {
            match io.load(ses_buf, off) {
                Ok((h, used)) => {
                    if h != tbl.session_at(i) {
                        flush_all(tbl, io);
                        return Err(IoErr::Integrity);
                    }
                    off += used;
                }
                Err(IoErr::NotFound) => {
                    tbl.clear_session(i);
                }
                Err(e) => {
                    flush_all(tbl, io);
                    return Err(e);
                }
            }
        }
    }
    Ok(())
}
/// 把芯片上属于本 space 的东西全部保存回备份缓冲区并释放。
///
/// 成功返回后表中不再有活跃槽位，芯片上不再持有本 space 的瞬态对象——
/// 这正是「事务结束后芯片是干净的」这条性质。
pub fn save_space<I: ContextIo>(
    tbl: &mut SpaceTable,
    io: &mut I,
    ctx_buf: &mut [u8],
    ses_buf: &mut [u8],
) -> Result<(), IoErr> {
    let mut off: usize = 0;
    for i in 0..SLOTS {
        if let CtxSlot::Live(h) = tbl.slot_at(i) {
            match io.save(h, ctx_buf, off) {
                Ok(used) => {
                    io.flush(h);
                    tbl.set_slot_free(i, true);
                    off += used;
                }
                Err(IoErr::NotFound) => {
                    tbl.set_slot_free(i, false);
                }
                Err(e) => {
                    flush_all(tbl, io);
                    return Err(e);
                }
            }
        }
    }
    let mut off: usize = 0;
    for i in 0..SLOTS {
        let h = tbl.session_at(i);
        if h != 0 {
            match io.save(h, ses_buf, off) {
                Ok(used) => {
                    off += used;
                }
                Err(IoErr::NotFound) => {
                    tbl.clear_session(i);
                }
                Err(e) => {
                    flush_all(tbl, io);
                    return Err(e);
                }
            }
        }
    }
    Ok(())
}
