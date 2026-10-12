#![no_std]

extern crate alloc;

mod buf;
pub mod chip;
pub mod cmd;
mod compat;
pub mod cursor;
mod endian;
mod handle;
pub mod module;
pub mod msg;
pub mod probe;
pub mod rewrite;
pub mod rsp;
pub mod table;
pub mod types;

// 会话授权层：可信密码学规约 -> 授权区编解码 -> 会话状态机
pub mod auth;
pub mod crypto;
pub mod session;

// 硬件层：寄存器语义 -> 物理接触面 -> 硬件状态机
pub mod mmio;
pub mod phy;
pub mod tis;
mod tis_core;

pub mod crb;
mod crb_core;
mod crb_phy;

pub use crb::{CrbErr, MAX_LOCALITY as CRB_MAX_LOCALITY};
pub use crb_core::Crb;
pub use crb_phy::CrbPhy;
// 编排层：长度校验、重传、返回码提取 -> 幽灵账本与链路接合
mod link;
pub mod xfer;

// 授权往返：把「响应必须先过 MAC 校验」变成类型层面的事实
mod secure;

// 引导序列：宿主接口自检 -> 启动 -> 自检 -> 容量对账
mod boot;

// 阶段移交：链路在无会话路径与授权路径之间易手，账本一路随行
mod handoff;

pub use auth::{AuthErr, RspAuth, SA_CONTINUE_SESSION, SA_DECRYPT, SA_ENCRYPT};
pub use boot::{Boot, BootErr, Limits, bring_up};
pub use buf::{BufKind, TPM_HEADER_SIZE, TPM2B_HEADER_SIZE, TpmBuf};
pub use crypto::{AesCfb, HmacSha256Ctx, NONCE_LEN, NonceSource, SHA256_LEN, Sha256Ctx};
pub use handoff::{attach, close_ctx, open_ctx, to_auth, to_plain};
pub use link::{ChipLink, LiveSet};
pub use mmio::TisMmio;
pub use phy::TisPhy;
pub use secure::{Authenticated, CmdLayout, Guarded, SecErr};
pub use session::{AuthSession, SessionState};
pub use tis::{MAX_LOCALITY, TisErr};
pub use tis_core::Tis;
pub use types::{TpmRc, TpmTag};
pub use xfer::{Xfer, XferErr};
