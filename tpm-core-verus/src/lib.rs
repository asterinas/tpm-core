#![no_std]
#![allow(unused_imports)]

pub mod probe;
mod buf;
mod endian;
pub mod types;
pub mod cursor;
pub mod msg;
pub mod cmd;
pub mod rsp;
mod handle;
pub mod module;
pub mod rewrite;
pub mod table;
pub mod chip;

// Session authorization layer: trusted crypto spec -> authorization area codec -> session state machine
pub mod crypto;
pub mod auth;
pub mod session;

// Hardware layer: register semantics -> physical interface -> hardware state machine
pub mod tis;
pub mod phy;
pub mod mmio;
mod tis_core;

pub mod crb;
mod crb_phy;
mod crb_core;

pub use crb::{CrbErr, MAX_LOCALITY as CRB_MAX_LOCALITY};
pub use crb_phy::CrbPhy;
pub use crb_core::Crb;
// Orchestration layer: length checks, retransmission, return-code extraction -> ghost ledger and link wiring
pub mod xfer;
mod link;

// Authorized round trip: make "a response must pass MAC verification first" a type-level fact
mod secure;

// Boot sequence: host interface self-check -> startup -> self-test -> capacity reconciliation
mod boot;

// Phase handoff: the link changes hands between the session-less and authorized paths, with the ledger traveling along
mod handoff;

pub use buf::{BufKind, TpmBuf, TPM2B_HEADER_SIZE, TPM_HEADER_SIZE};
pub use types::{TpmRc, TpmTag};
pub use auth::{AuthErr, RspAuth, SA_CONTINUE_SESSION, SA_DECRYPT, SA_ENCRYPT};
pub use crypto::{AesCfb, HmacSha256Ctx, NonceSource, Sha256Ctx, NONCE_LEN, SHA256_LEN};
pub use session::{AuthSession, SessionState};
pub use tis::{TisErr, MAX_LOCALITY};
pub use tis_core::Tis;
pub use phy::TisPhy;
pub use mmio::TisMmio;
pub use xfer::{Xfer, XferErr};
pub use link::{ChipLink, LiveSet};
pub use secure::{Authenticated, CmdLayout, Guarded, SecErr};
pub use boot::{bring_up, Boot, BootErr, Limits};
pub use handoff::{attach, close_ctx, open_ctx, to_auth, to_plain};