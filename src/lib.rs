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

// Session authorization layer: trusted cryptographic protocol -> authorization-area encoding/decoding -> session state machine
pub mod auth;
pub mod crypto;
pub mod session;

// Hardware layer: register semantics -> physical interface -> hardware state machine
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
// Coordination layer: length validation, retransmission, return-code extraction -> ghost ledger and link integration
mod link;
pub mod xfer;

// Authorized round-trip: turn “the response must pass MAC validation first” into a type-level fact
mod secure;

// Boot sequence: host interface self-test -> startup -> self-test -> capacity reconciliation
mod boot;

// Phase handoff: the link moves between the no-session path and the authorized path while the ledger follows along
mod handoff;

pub use auth::{AuthErr, RspAuth, SA_CONTINUE_SESSION, SA_DECRYPT, SA_ENCRYPT};
pub use boot::{bring_up, Boot, BootErr, Limits};
pub use buf::{BufKind, TpmBuf, TPM2B_HEADER_SIZE, TPM_HEADER_SIZE};
pub use crypto::{AesCfb, HmacSha256Ctx, NonceSource, Sha256Ctx, NONCE_LEN, SHA256_LEN};
pub use handoff::{attach, close_ctx, open_ctx, to_auth, to_plain};
pub use link::{ChipLink, LiveSet};
pub use mmio::TisMmio;
pub use phy::TisPhy;
pub use secure::{Authenticated, CmdLayout, Guarded, SecErr};
pub use session::{AuthSession, SessionState};
pub use tis::{TisErr, MAX_LOCALITY};
pub use tis_core::Tis;
pub use types::{TpmRc, TpmTag};
pub use xfer::{Xfer, XferErr};
