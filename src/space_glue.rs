//! 句柄空间的胶水层。
//!
//! 归属 `tpm-module`，不进 Verus。这里只做两件验证层刻意不碰的事：
//! 分配备份缓冲区，以及让**字节缓冲区的事务边界与表的事务边界重合**。
//!
//! 后一件是本文件存在的唯一理由。`Transaction` 保证了表的原子性——改动
//! 落在副本上，只有 `commit` 才写回。但备份缓冲区是两块十几 KiB 的字节
//! 数组，把它们塞进 `tpm-core` 会让每个证明都拖着两个大数组的 `Seq`，
//! 而它们的语义无非是「一起提交或一起丢弃」。所以副本留在这里，规则由
//! 类型强制：拿到 `Work` 的唯一途径是 `begin`，`Work` 没有 `Clone`，
//! 提交与回滚都按值取走它。

use tpm_core::module::{ContextIo, IoErr, Space, Transaction, load_space, save_space};
use tpm_core::rewrite::{SpaceErr, map_capability_handles, map_command_handles, map_response_handle};
use tpm_core::table::SpaceTable;

/// 单个 space 的上下文备份容量。两块缓冲区分别存对象与会话。
pub const CTX_BUF_SIZE: usize = 16 * 1024;

pub struct SpaceStore {
    space: Space,
    ctx: [u8; CTX_BUF_SIZE],
    ses: [u8; CTX_BUF_SIZE],
}

/// 一次请求期间的完整工作副本：表 + 两块备份缓冲区。
///
/// 没有 `Clone`，没有公开构造函数。丢弃它就是回滚。
pub struct Work {
    txn: Transaction,
    ctx: [u8; CTX_BUF_SIZE],
    ses: [u8; CTX_BUF_SIZE],
}

impl SpaceStore {
    pub fn new() -> Self {
        SpaceStore { space: Space::new(), ctx: [0u8; CTX_BUF_SIZE], ses: [0u8; CTX_BUF_SIZE] }
    }

    /// 取工作副本。表的复制由 `tpm-core` 负责，两次 memcpy 在这里。
    pub fn begin(&self) -> Work {
        Work { txn: self.space.begin(), ctx: self.ctx, ses: self.ses }
    }

    /// 整条路径成功后一次性写回。表与缓冲区在同一个函数里落笔，
    /// 中间没有可以观察到「表已更新而缓冲区未更新」的时刻。
    pub fn commit(&mut self, w: Work) {
        self.ctx = w.ctx;
        self.ses = w.ses;
        self.space.commit(w.txn);
    }

    /// 失败收尾：释放芯片上的残留，丢弃副本。
    pub fn rollback<I: ContextIo>(&self, w: Work, io: &mut I) {
        w.txn.abort(io);
        // 两块缓冲区随 `w` 一起离开作用域，稳定状态原封未动。
    }
}

#[derive(Debug)]
pub enum SpaceError {
    Io(IoErr),
    Cmd(SpaceErr),
}

impl Work {
    fn table(&mut self) -> &mut SpaceTable {
        self.txn.table()
    }
}

/// 一次请求的完整时序。
///
/// 参数 `nr_handles`、`has_rhandle`、`is_cap_query` 都来自命令属性表，
/// 属于编解码层的产物；这里只负责按顺序把它们喂给验证过的函数，并保证
/// 任何一步失败都走同一条回滚路径。
pub fn run_request<I, F>(
    store: &mut SpaceStore,
    io: &mut I,
    nr_handles: usize,
    has_rhandle: bool,
    is_cap_query: bool,
    cmd: &mut [u8],
    rsp: &mut [u8],
    transmit: F,
) -> Result<usize, SpaceError>
where
    I: ContextIo,
    F: FnOnce(&[u8], &mut [u8]) -> Result<usize, IoErr>,
{
    let mut w = store.begin();

    macro_rules! bail {
        ($e:expr) => {{
            store.rollback(w, io);
            return Err($e);
        }};
    }

    // 1. 把上一轮换出的对象装回芯片
    if let Err(e) = load_space(w.table(), io, &w.ctx, &w.ses) {
        bail!(SpaceError::Io(e));
    }

    // 2. 命令方向：虚拟句柄 → 物理句柄
    if let Err(e) = map_command_handles(w.table(), nr_handles, cmd) {
        bail!(SpaceError::Cmd(e));
    }

    // 3. 下发
    let n = match transmit(cmd, rsp) {
        Ok(n) => n,
        Err(e) => bail!(SpaceError::Io(e)),
    };

    // 4. 响应方向：登记新句柄、改写句柄区
    match map_response_handle(w.table(), has_rhandle, rsp) {
        outcome if needs_flush(&outcome) => {
            // 表满：句柄接管不了，必须在这里释放，否则它会永久占着芯片资源
            if let Some(h) = flush_target(&outcome) {
                io.flush(h);
            }
            bail!(SpaceError::Io(IoErr::NoSpace));
        },
        _ => {},
    }
    let n = match map_capability_handles(w.table(), is_cap_query, rsp, n) {
        Ok(n) => n,
        Err(e) => bail!(SpaceError::Cmd(e)),
    };

    // 5. 换出：芯片恢复干净，内容落回工作副本
    if let Err(e) = save_space(w.table(), io, &mut w.ctx, &mut w.ses) {
        bail!(SpaceError::Io(e));
    }

    // 6. 只有走到这里才写回
    store.commit(w);
    Ok(n)
}

use tpm_core::rewrite::HeaderOutcome;

fn needs_flush(o: &HeaderOutcome) -> bool {
    matches!(o, HeaderOutcome::OutOfSlots { .. })
}

fn flush_target(o: &HeaderOutcome) -> Option<u32> {
    match o {
        HeaderOutcome::OutOfSlots { flush } => Some(*flush),
        _ => None,
    }
}
