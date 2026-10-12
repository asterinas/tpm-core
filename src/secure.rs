use crate::{
    auth::{AuthErr, RspAuth, write_cmd_session},
    chip::MSG_MAX,
    crypto::{HmacSha256Ctx, NonceSource, Sha256Ctx},
    phy::TisPhy,
    session::AuthSession,
    xfer::{RC_SUCCESS, Xfer, XferErr},
};

/// 一条带授权的命令在缓冲区里的分区。
///
/// 由调用方给出而不是由本层推算：分区取决于具体命令有几个句柄、参数怎么排，
/// 那是命令层的知识。本层只负责**核对这些分区互不冲突**，然后照着填。
pub struct CmdLayout {
    /// 命令总长度。必须与报文头里的长度字段一致，这一点由链路层复核。
    pub len: usize,
    /// 授权区起点。
    pub sess_off: usize,
    /// 本会话在授权区里的序号。
    pub index: usize,
    /// 参数区起点。
    pub param_off: usize,
    /// 参数区长度。
    pub param_len: usize,
    /// 响应里的句柄个数。摘要覆盖的是句柄之后的部分，数错一个，整段偏移全错。
    pub rhandles: usize,
}
/// 一枚「这段响应的 MAC 已经对上」的凭证。
///
/// 定位结果 `a` 可以公开：读几个偏移不构成任何能力，能力在于凭证本身——
/// 只有 [`Guarded::invoke`] 校验通过后才会铸出它，`#[non_exhaustive]` 则保证
/// 模块外无法凭空构造一枚。
#[non_exhaustive]
pub struct Authenticated {
    pub a: RspAuth,
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SecErr {
    /// 字节没能走完一个来回。
    Bus(XferErr),
    /// 器件返回了非零返回码。这类响应不带授权区，无从校验。
    Rc(u32),
    /// 响应到了，但授权校验没过。
    Auth(AuthErr),
}
pub struct Guarded<P: TisPhy> {
    x: Xfer<P>,
    sess: AuthSession,
    /// 响应暂存区。本层的全部保证都建立在模块之外拿不到它之上。
    rbuf: [u8; MSG_MAX],
}
impl<P: TisPhy> Guarded<P> {
    pub fn new(x: Xfer<P>, sess: AuthSession) -> Self {
        Guarded {
            x,
            sess,
            rbuf: [0u8; MSG_MAX],
        }
    }
    /// 发一条带授权的命令，只有 MAC 对上才返回。
    ///
    /// 调用方需要事先把报文头、句柄区、参数区写好，并按 `lay` 留出授权区。
    /// 授权区由本函数填写——它含有本轮 nonce，而 nonce 要到换取那一刻才产生，
    /// 调用方提前填不了。
    ///
    /// 失败路径一律作废会话。会话失败之后拿同一把密钥重试，等于给对面多一次
    /// 猜测机会；作废之后要重新握手，代价是一次往返，换来的是猜测机会不累积。
    pub fn invoke<S: Sha256Ctx, H: HmacSha256Ctx, R: NonceSource>(
        &mut self,
        rng: &mut R,
        cmd: &mut [u8],
        lay: CmdLayout,
        names: &[u8],
        ordinal: u32,
        attrs: u8,
    ) -> Result<Authenticated, SecErr> {
        self.sess.begin(rng, ordinal, attrs);
        let handle = self.sess.handle();
        let nonce = self.sess.our_nonce();
        let sattrs = self.sess.attrs();
        write_cmd_session(cmd, lay.sess_off, handle, &nonce, sattrs);
        self.sess.finalize::<S, H>(
            cmd,
            lay.sess_off,
            lay.index,
            names,
            lay.param_off,
            lay.param_len,
        );
        let n = match self.x.run(&*cmd, lay.len, &mut self.rbuf) {
            Ok((n, rc)) => {
                if rc != RC_SUCCESS {
                    self.sess.close();
                    return Err(SecErr::Rc(rc));
                }
                n
            }
            Err(e) => {
                self.sess.close();
                return Err(SecErr::Bus(e));
            }
        };
        let raw = &self.rbuf[0..n];
        let a = match self.sess.check_response::<S, H>(raw, lay.rhandles) {
            Ok(a) => a,
            Err(e) => return Err(SecErr::Auth(e)),
        };
        Ok(Authenticated { a })
    }
    /// 取出响应的参数区。
    ///
    /// 这是响应字节离开本结构体的**唯一出口**。前置条件要出示一枚与当前
    /// 暂存区内容匹配的凭证：没有凭证拿不到字节，凭证过期也拿不到。
    pub fn params<'a>(&'a self, t: &Authenticated) -> &'a [u8] {
        let off = t.a.param_off;
        let len = t.a.param_len;
        &self.rbuf[off..off + len]
    }
    /// 响应参数区的长度。凭证已经把它固定下来，读取前不必再解析一次报文。
    pub fn param_len(&self, t: &Authenticated) -> usize {
        t.a.param_len
    }
    /// 交回链路，结束授权阶段。
    ///
    /// 会话随 `self` 一起消失，这正是想要的：一个不再持有链路的会话，nonce
    /// 链条已经断了，留着只会让「拿旧会话继续说话」在类型上看起来可行。
    /// 响应暂存区一并释放，此前铸出的凭证也就再没有对应的报文可读——那些
    /// 凭证的前置条件要求报文与铸造时刻逐字节相同，而报文已经不在了。
    pub fn release(self) -> Xfer<P> {
        self.x
    }
}
