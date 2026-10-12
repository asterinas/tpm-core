use crate::{
    chip::{ChipTransport, RC_SUCCESS},
    cmd::{CC_CONTEXT_LOAD, CC_FLUSH_CONTEXT},
    module::IoErr,
    phy::TisPhy,
    rewrite::HEADER_SIZE,
    xfer::{Xfer, XferErr, peek_be32},
};

/// 芯片当前持有的句柄集合。
///
/// 只有幽灵字段，运行时是零大小类型。所有修改它的方法都不含可执行代码——
/// 它们不是在「记录」什么，而是在**声明本端对芯片行为的假设**。
pub struct LiveSet;
impl LiveSet {
    pub fn new() -> Self {
        Self
    }
    pub fn observe_load(&mut self, _h: u32) {}
    pub fn observe_flush(&mut self) {}
}

impl Default for LiveSet {
    fn default() -> Self {
        Self::new()
    }
}
pub struct ChipLink<P: TisPhy> {
    pub x: Xfer<P>,
    pub ledger: LiveSet,
}
impl<P: TisPhy> ChipLink<P> {
    pub fn new(x: Xfer<P>) -> Self {
        ChipLink {
            x,
            ledger: LiveSet::new(),
        }
    }
}
impl<P: TisPhy> ChipTransport for ChipLink<P> {
    fn exec(&mut self, cmd: &[u8], rsp: &mut [u8]) -> Result<usize, IoErr> {
        let cc = peek_be32(cmd, 6);
        if cc == CC_FLUSH_CONTEXT {
            self.ledger.observe_flush();
        }
        if !self.x.ready() {
            return Err(IoErr::NotReady);
        }
        let declared = peek_be32(cmd, 2);
        if declared < HEADER_SIZE as u32 {
            return Err(IoErr::BadCommand);
        }
        let len = declared as usize;
        if len > cmd.len() {
            return Err(IoErr::BadCommand);
        }
        let n = match self.x.run(cmd, len, rsp) {
            Ok((n, rc)) => {
                if cc == CC_CONTEXT_LOAD && rc == RC_SUCCESS {
                    if n < HEADER_SIZE + 4 {
                        return Err(IoErr::Protocol);
                    }
                    let h = peek_be32(&*rsp, HEADER_SIZE);
                    self.ledger.observe_load(h);
                }
                n
            }
            Err(e) => {
                return Err(map_err(e));
            }
        };
        Ok(n)
    }
}
/// 链路错误 → 编排层错误。
///
/// 链路层失败没有返回码可读，因此这里只做「传输语义」上的分类：
/// 超时可重试，物理故障不可重试，协议帧不可信，命令自描述不自洽。
pub fn map_err(e: XferErr) -> IoErr {
    match e {
        XferErr::Bus(crate::tis::TisErr::Phy) => IoErr::Bus,
        XferErr::Bus(crate::tis::TisErr::Timeout) => IoErr::Timeout,
        XferErr::Bus(crate::tis::TisErr::Protocol) => IoErr::Protocol,
        XferErr::Bus(crate::tis::TisErr::BadLength) => IoErr::Protocol,
        XferErr::BadCommand => IoErr::BadCommand,
    }
}
