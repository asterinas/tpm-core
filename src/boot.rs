use crate::{
    chip::MSG_MAX,
    cmd::{CAP_TPM_PROPERTIES, CC_GET_CAPABILITY, CC_SELF_TEST, CC_SHUTDOWN, CC_STARTUP},
    cursor::{be16_bytes, be32_bytes},
    msg::{ParseError, RC_SUCCESS, ST_NO_SESSIONS, TPM_HEADER_LEN, build_header, parse_response},
    phy::TisPhy,
    rsp::parse_tpm_property,
    xfer::{Xfer, XferErr},
};

/// 器件尚未初始化，或者反过来——已经初始化过了。
///
/// 它出现在启动命令的响应里时，含义是「这条命令来晚了，器件早已启动」。
/// 引导层把它按成功处理，见 [`Boot::startup`] 的说明。
const RC_INITIALIZE: u32 = 0x0000_0100;
/// 自检正在后台进行。
pub const RC_TESTING: u32 = 0x0000_090A;
/// 器件能接收的最长命令。
const PT_MAX_COMMAND_SIZE: u32 = 0x0000_011E;
/// 器件能产生的最长响应。
const PT_MAX_RESPONSE_SIZE: u32 = 0x0000_011F;
/// 单个对象备份块的最大长度。
const PT_MAX_OBJECT_CONTEXT: u32 = 0x0000_0121;
/// 单个会话备份块的最大长度。
const PT_MAX_SESSION_CONTEXT: u32 = 0x0000_0122;
const SELF_TEST_FULL: u8 = 1;
const SELF_TEST_INCREMENTAL: u8 = 0;
/// 引导命令的最长者：报文头 10 字节 + 能力查询的三个 u32。
const BOOT_CMD_MAX: usize = 22;
/// 引导响应的容量。单条属性的应答是报文头 10 + 定长前缀 9 + 一对键值 8 =
/// 27 字节；取 128 留出余量，同时把这块暂存区压得足够小，可以安心放在栈上。
const BOOT_RSP_MAX: usize = 128;
#[derive(PartialEq, Eq)]
pub enum BootErr {
    /// 宿主提供的密码学接口与本驱动的假设对不上。
    Abi,
    /// 链路不处于可以发起命令的状态。
    NotReady,
    /// 字节没能走完一个来回。
    Bus(XferErr),
    /// 器件给出了非零返回码。
    Rc(u32),
    /// 响应到了，但解析不通过。
    Parse(ParseError),
    /// 器件自述的容量超出本驱动静态预留的空间。
    Capacity,
}
/// 引导期问出来的四个尺寸。
///
/// 问它们不是为了记录，而是为了**对账**：本驱动的缓冲区都是定长的，尺寸在
/// 编译期就定死了；器件若要求更大的报文，或者产出的备份块比预留空间长，那
/// 是一个必须在引导期就暴露的不匹配。拖到运行期，症状是某条特定命令偶发
/// 截断，与容量二字毫无表面联系。
pub struct Limits {
    pub max_command: u32,
    pub max_response: u32,
    pub max_object_context: u32,
    pub max_session_context: u32,
}
pub struct Boot<P: TisPhy> {
    x: Xfer<P>,
    /// 命令暂存区。私有：本层对报文长度字段的全部保证，都建立在外部改不动
    /// 它之上。
    cbuf: [u8; BOOT_CMD_MAX],
    rbuf: [u8; BOOT_RSP_MAX],
}
impl<P: TisPhy> Boot<P> {
    pub fn new(x: Xfer<P>) -> Self {
        Boot {
            x,
            cbuf: [0u8; BOOT_CMD_MAX],
            rbuf: [0u8; BOOT_RSP_MAX],
        }
    }
    /// 交出链路，结束引导阶段。
    pub fn finish(self) -> Xfer<P> {
        self.x
    }
    /// 写入报文头。
    ///
    /// 长度字段在这里一次性写死，之后不再回填。引导命令的载荷长度全部是编译期
    /// 常量，没有「先写载荷、再看写了多长」的必要——而回填恰恰是长度字段与实际
    /// 字节数走散的唯一入口。
    fn put_header(&mut self, cc: u32, total: usize) {
        let hdr = build_header(ST_NO_SESSIONS, cc, total as u32);
        self.cbuf[..TPM_HEADER_LEN].copy_from_slice(&hdr);
    }
    /// 写一个字节的载荷。
    fn put_u8(&mut self, off: usize, v: u8) {
        self.cbuf[off] = v;
    }
    /// 写一个大端 u16 载荷。
    fn put_be16(&mut self, off: usize, v: u16) {
        let b = be16_bytes(v);
        self.cbuf[off] = b[0];
        self.cbuf[off + 1] = b[1];
    }
    /// 写一个大端 u32 载荷。
    fn put_be32(&mut self, off: usize, v: u32) {
        let b = be32_bytes(v);
        self.cbuf[off] = b[0];
        self.cbuf[off + 1] = b[1];
        self.cbuf[off + 2] = b[2];
        self.cbuf[off + 3] = b[3];
    }
    /// 把已拼好的命令发出去，取回响应长度与返回码。
    ///
    /// 前置条件里那句「长度字段等于 `len`」不是形式上的讲究：链路层会对着这个
    /// 字段决定往总线上推多少字节，字段与实参一旦不符，器件与本端就会各等各的，
    /// 一直等到超时。在这里写成前置条件，等于把这件事交给拼装函数的后置条件去
    /// 保证，而不是寄望于每个调用点自己记得。
    fn exec(&mut self, len: usize) -> Result<(usize, u32), BootErr> {
        if !self.x.ready() {
            return Err(BootErr::NotReady);
        }
        match self.x.run(&self.cbuf, len, &mut self.rbuf) {
            Ok((n, rc)) => Ok((n, rc)),
            Err(e) => Err(BootErr::Bus(e)),
        }
    }
    /// 宣告本端的启动方式。
    ///
    /// 「已经启动过了」按成功处理。器件的启动状态由上电周期决定，而本端可能
    /// 是在器件已被更早的一段固件初始化之后才接手的——这种情形下重发一条启动
    /// 命令得到的拒绝，说的是「你要的状态已经成立」，把它当失败会让驱动在一类
    /// 完全正常的平台上直接拒绝加载。
    ///
    /// 反过来，其余任何非零返回码都如实上报，不做二次解释。
    pub fn startup(&mut self, su: u16) -> Result<(), BootErr> {
        let total = TPM_HEADER_LEN + 2;
        self.put_header(CC_STARTUP, total);
        self.put_be16(TPM_HEADER_LEN, su);
        match self.exec(total) {
            Ok((_n, rc)) => {
                if rc == RC_SUCCESS || rc == RC_INITIALIZE {
                    Ok(())
                } else {
                    Err(BootErr::Rc(rc))
                }
            }
            Err(e) => Err(e),
        }
    }
    /// 关机。
    ///
    /// 与启动不同，这里不放过任何非零返回码：关机若没成功，器件下次上电会
    /// 认为上一轮是异常断电，进而重置一部分状态。这件事调用方必须知道。
    pub fn shutdown(&mut self, su: u16) -> Result<(), BootErr> {
        let total = TPM_HEADER_LEN + 2;
        self.put_header(CC_SHUTDOWN, total);
        self.put_be16(TPM_HEADER_LEN, su);
        match self.exec(total) {
            Ok((_n, rc)) => {
                if rc == RC_SUCCESS {
                    Ok(())
                } else {
                    Err(BootErr::Rc(rc))
                }
            }
            Err(e) => Err(e),
        }
    }
    /// 触发自检。`full` 为真时要求重测全部算法，否则只测尚未测过的部分。
    ///
    /// 「正在测」按成功处理，理由与启动那条不同：这条命令的语义本就是「开始测」
    /// 而非「测完了」，器件回一句还在测，恰恰说明命令生效了。真正的自检结论要
    /// 另行查询，本层不代劳——把「已开始」与「已通过」混成一个返回值，会让调用
    /// 方以为拿到了后者。
    pub fn self_test(&mut self, full: bool) -> Result<(), BootErr> {
        let total = TPM_HEADER_LEN + 1;
        self.put_header(CC_SELF_TEST, total);
        let arg = if full {
            SELF_TEST_FULL
        } else {
            SELF_TEST_INCREMENTAL
        };
        self.put_u8(TPM_HEADER_LEN, arg);
        match self.exec(total) {
            Ok((_n, rc)) => {
                if rc == RC_SUCCESS || rc == RC_TESTING {
                    Ok(())
                } else {
                    Err(BootErr::Rc(rc))
                }
            }
            Err(e) => Err(e),
        }
    }
    /// 问一个固定属性的值。
    ///
    /// 一次只问一个。批量查询能省几次往返，但应答里的键值对顺序由器件决定，
    /// 逐条对号入座的代码要处理缺项、乱序、重复三种情况，而引导期一共只问
    /// 四个属性——省下的往返换不来这些分支。
    pub fn property(&mut self, pt: u32) -> Result<u32, BootErr> {
        let total = TPM_HEADER_LEN + 12;
        self.put_header(CC_GET_CAPABILITY, total);
        self.put_be32(TPM_HEADER_LEN, CAP_TPM_PROPERTIES);
        self.put_be32(TPM_HEADER_LEN + 4, pt);
        self.put_be32(TPM_HEADER_LEN + 8, 1);
        let n = match self.exec(total) {
            Ok((n, rc)) => {
                if rc != RC_SUCCESS {
                    return Err(BootErr::Rc(rc));
                }
                n
            }
            Err(e) => return Err(e),
        };
        let raw = &self.rbuf[0..n];
        let rsp = parse_response(raw).map_err(BootErr::Parse)?;
        parse_tpm_property(rsp.body).map_err(BootErr::Parse)
    }
    /// 问齐四个尺寸，并与本驱动的静态预留对账。
    ///
    /// 对账不通过就报错，不做降级。降级意味着运行期存在一条「缓冲区不够，
    /// 于是分片 / 截断 / 跳过」的路径，而那条路径在容量充足的机器上永远不会
    /// 被执行到，也就永远不会被测到。宁可在这里拒绝加载。
    pub fn probe_limits(&mut self) -> Result<Limits, BootErr> {
        let max_command = self.property(PT_MAX_COMMAND_SIZE)?;
        let max_response = self.property(PT_MAX_RESPONSE_SIZE)?;
        let max_object_context = self.property(PT_MAX_OBJECT_CONTEXT)?;
        let max_session_context = self.property(PT_MAX_SESSION_CONTEXT)?;
        if max_response as usize > MSG_MAX {
            return Err(BootErr::Capacity);
        }
        if max_object_context as usize > MSG_MAX {
            return Err(BootErr::Capacity);
        }
        if max_session_context as usize > MSG_MAX {
            return Err(BootErr::Capacity);
        }
        Ok(Limits {
            max_command,
            max_response,
            max_object_context,
            max_session_context,
        })
    }
}
/// 从一条刚建立的链路走到「可以承载业务」，顺带交出器件容量。
///
/// 顺序由依赖关系定死，不是习惯：
///
/// 1. **宿主接口自检的结果**由调用方通过 `abi_ok` 给入,在这里最先裁决。
///    自检本身不需要器件参与,也不属于本层职责——它触及外部接口,该由落地层
///    去做;本层只负责「接口对不上就别往下走」。之所以排最前,是因为接口对不上
///    时后面每一步都会以难以归因的方式出错,不如在一个字节都还没发出去的时候
///    就停下。
/// 2. **启动**。器件在收到启动命令之前，对绝大多数命令的应答都是拒绝。
/// 3. **自检**。要在有业务命令进来之前触发，让它与后续操作并行进行。
/// 4. **容量对账**。放在最后，因为它是唯一一个需要解析应答载荷的步骤，
///    而载荷解析要求器件已经处于正常工作状态。
///
/// 中途任何一步失败都直接返回，链路随之被丢弃。这一层没有「部分成功」这种
/// 状态——引导没走完的器件，本端说不出它现在处于哪里。
pub fn bring_up<P: TisPhy>(
    x: Xfer<P>,
    su: u16,
    abi_ok: bool,
) -> Result<(Xfer<P>, Limits), BootErr> {
    if !abi_ok {
        return Err(BootErr::Abi);
    }
    let mut b = Boot::new(x);
    match b.startup(su) {
        Ok(()) => {}
        Err(e) => return Err(e),
    }
    match b.self_test(false) {
        Ok(()) => {}
        Err(e) => return Err(e),
    }
    let lim = b.probe_limits()?;
    Ok((b.finish(), lim))
}
