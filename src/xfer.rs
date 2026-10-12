use crate::{
    cmd::{
        CC_CONTEXT_LOAD, CC_CONTEXT_SAVE, CC_FLUSH_CONTEXT, CC_GET_CAPABILITY, CC_GET_RANDOM,
        CC_PCR_EXTEND, CC_PCR_READ, CC_SELF_TEST, CC_SHUTDOWN, CC_STARTUP,
    },
    msg::TPM_HEADER_LEN,
    phy::TisPhy,
    rewrite::read_be32,
    tis::{TisErr, budget_of},
    tis_core::Tis,
};

pub const RC_SUCCESS: u32 = 0x0000_0000;
/// 警告类返回码的基址。位 11 置位表示「不是失败，是暂时不能办」。
pub const RC_WARN_BASE: u32 = 0x0000_0900;
/// 器件正在自检，被请求的功能尚未就绪。
pub const RC_TESTING: u32 = 0x0000_090A;
/// 器件当前忙，请稍后重发同一条命令。
pub const RC_RETRY: u32 = 0x0000_0922;
/// 器件主动让出，命令未执行。语义上与 [`RC_RETRY`] 同类，但它由器件的调度
/// 策略触发而非资源短缺，重发一次通常就能过。
pub const RC_YIELDED: u32 = 0x0000_0908;
/// 首次退避的时长（毫秒）。
const RETRY_FIRST_MS: u32 = 20;
/// 单次退避的时长上限（毫秒）。
const RETRY_CAP_MS: u32 = 2000;
/// 重传次数上限。取到这个数之后仍是可重试返回码，就把它原样交给调用方——
/// 本层不把「等了很久还是忙」翻译成错误，那是调用方该拿的判断。
const RETRY_MAX: u32 = 8;
const DURATION_SHORT_MS: u32 = 750;
const DURATION_MEDIUM_MS: u32 = 2000;
const DURATION_LONG_MS: u32 = 30000;
/// 未列出命令的默认上界。取得很大是有意的：一条本层不认识的命令，本层也就
/// 没有依据说它该多快。
const DURATION_DEFAULT_MS: u32 = 120000;
/// 命令码 → 执行时长上界（毫秒）。
///
/// 返回值恒为正，因此 [`budget_of`] 折算出的轮询预算恒不为零。
fn duration_ms(cc: u32) -> u32 {
    if cc == CC_STARTUP
        || cc == CC_SHUTDOWN
        || cc == CC_PCR_READ
        || cc == CC_PCR_EXTEND
        || cc == CC_GET_CAPABILITY
        || cc == CC_CONTEXT_LOAD
        || cc == CC_CONTEXT_SAVE
        || cc == CC_FLUSH_CONTEXT
    {
        DURATION_SHORT_MS
    } else if cc == CC_GET_RANDOM {
        DURATION_MEDIUM_MS
    } else if cc == CC_SELF_TEST {
        DURATION_LONG_MS
    } else {
        DURATION_DEFAULT_MS
    }
}
/// 命令码 → 等待响应的轮询预算。
pub fn poll_budget(cc: u32) -> u32 {
    budget_of(duration_ms(cc))
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum XferErr {
    /// 传输层报错。字节没能完整走完一个来回。
    Bus(TisErr),
    /// 命令自身不成立：长度字段与缓冲区对不上。命令一个字节都没有发出。
    BadCommand,
}
/// 大端 u32 读取，同时给出两种规约写法下的值。
///
/// 报文头由命令层生成（规约用乘加形式），句柄区由重写层读取（规约用移位或
/// 形式），本层横跨两者，读一次就把两种形式都摆出来，免得每个调用点各自
/// 引一遍桥引理。
pub(crate) fn peek_be32(b: &[u8], off: usize) -> u32 {
    read_be32(b, off)
}
fn cmd_wf(cmd: &[u8], len: usize) -> bool {
    if len < TPM_HEADER_LEN {
        return false;
    }
    if len > cmd.len() {
        return false;
    }
    let d = peek_be32(cmd, 2);
    d as usize == len
}
/// 响应体（报文头之后的部分）不短于 `min_body`。
///
/// 单独列出来是因为它是**解析前的最后一道闸**：解析函数一律以「体长足够」
/// 为前置条件，闸没关上，越界读取就从解析函数的内部实现细节变成了调用方的
/// 责任，而调用方通常忘了。
pub fn body_at_least(n: usize, min_body: usize) -> bool {
    n - TPM_HEADER_LEN >= min_body
}
pub struct Xfer<P: TisPhy> {
    pub tis: Tis<P>,
    /// 剩余可用的重传次数上限。做成字段而不是常量，是为了让引导阶段（器件
    /// 刚上电、自检未完）与稳态使用同一套代码而取不同的耐心。
    pub retries: u32,
}
impl<P: TisPhy> Xfer<P> {
    pub fn new(tis: Tis<P>) -> Self {
        Xfer {
            tis,
            retries: RETRY_MAX,
        }
    }
    /// 运行时自检：状态是否满足发起命令的前提。
    ///
    /// 存在的理由是接口边界——本层被一个不带前置条件的接口调用（那个接口的
    /// 签名由更上层的验证需要决定，改不动），而本层的方法有前置条件。差额只
    /// 能在运行时补上：查一次，不满足就直接报错，不让不满足前提的调用继续
    /// 往下走。
    pub fn ready(&self) -> bool {
        self.tis.locality < crate::tis::MAX_LOCALITY && !self.tis.held
    }
    /// 等待 `ticks` 个轮询间隔。
    ///
    /// 用轮询间隔的整数倍表示等待时长，而不是接一个睡眠接口：本层不引入
    /// 时间概念，等待的实际长度由物理层的节流实现决定。这条循环的终止性
    /// 因此直接来自计数器。
    fn backoff(&mut self, ticks: u32) {
        let mut left = ticks;
        while left > 0 {
            self.tis.phy.delay();
            left -= 1;
        }
    }
    /// 发一条命令，收一条响应，并取出返回码。
    ///
    /// 返回码取自响应头的固定偏移，取值不依赖任何报文体解析——响应长度已由
    /// 传输层保证不小于一个报文头，因此这次读取无条件成立。
    ///
    /// `exec_budget` 直接透传给 [`Tis::transmit`]，用于限定等待 `STS_DATA_AVAIL`
    /// 的轮询次数上界。
    fn attempt(
        &mut self,
        cmd: &[u8],
        len: usize,
        rsp: &mut [u8],
        exec_budget: u32,
    ) -> Result<(usize, u32), XferErr> {
        let n = self
            .tis
            .transmit(cmd, len, rsp, exec_budget)
            .map_err(XferErr::Bus)?;
        let rc = peek_be32(&*rsp, 6);
        Ok((n, rc))
    }
    /// 值得重发的返回码。
    ///
    /// 自检命令遇到「正在自检」是个例外：这条命令问的**就是**自检状态，
    /// 「还在测」是一个有效答案而非需要规避的应答。把它当作可重试会把一次
    /// 状态查询变成一段阻塞等待，引导阶段尤其不该这样。
    pub fn retryable(rc: u32, cc: u32) -> bool {
        if rc == RC_RETRY || rc == RC_YIELDED {
            true
        } else if rc == RC_TESTING {
            cc != CC_SELF_TEST
        } else {
            false
        }
    }
    /// 发一条命令，必要时重发，返回响应长度与返回码。
    ///
    /// 三条性质在签名里写死：
    ///
    /// - **命令没通过自检就一个字节都不发**。格式不良的命令在这里被挡下，
    ///   器件永远见不到它。
    /// - **无论走哪条出口，locality 都不再被持有**。这一条由传输层逐次保证，
    ///   重传只是把那个保证串起来——每次尝试都是一次完整的申请与归还，而不是
    ///   握着 locality 循环。多等几毫秒换整段等待期间其他 locality 可用，这笔
    ///   账是划算的。
    /// - **返回码就是响应头里的那个值**。本层不改写、不吞掉、不翻译；重传次数
    ///   耗尽之后仍是可重试返回码的，原样上交。
    ///
    /// 重发是安全的，因为命令缓冲区是只读的：本层拿到的是一个不可变切片，
    /// 从头到尾没有任何一步会修改它，所以第二次发送的字节与第一次逐字节相同。
    /// 若换成收发共用一个缓冲区，这一点就不再成立，重发前必须先恢复原文——
    /// 那是一个容易漏掉且很难在事后察觉的错误，分开两个缓冲区从根上避免了它。
    pub fn run(&mut self, cmd: &[u8], len: usize, rsp: &mut [u8]) -> Result<(usize, u32), XferErr> {
        if !cmd_wf(cmd, len) {
            return Err(XferErr::BadCommand);
        }
        let cc = peek_be32(cmd, 6);
        let exec_budget = poll_budget(cc);
        let cap = budget_of(RETRY_CAP_MS);
        let mut ticks = budget_of(RETRY_FIRST_MS);
        let mut left = self.retries;
        while left > 0 {
            match self.attempt(cmd, len, rsp, exec_budget) {
                Ok((n, rc)) => {
                    if !Self::retryable(rc, cc) {
                        return Ok((n, rc));
                    }
                }
                Err(e) => return Err(e),
            }
            self.backoff(ticks);
            if ticks < cap {
                if ticks <= cap - ticks {
                    ticks += ticks;
                } else {
                    ticks = cap;
                }
            }
            left -= 1;
        }
        self.attempt(cmd, len, rsp, exec_budget)
    }
}
