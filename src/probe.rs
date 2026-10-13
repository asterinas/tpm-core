use crate::{
    cmd::{CAP_TPM_PROPERTIES, CC_GET_CAPABILITY},
    cursor::be32_bytes,
    msg::{build_header, ST_NO_SESSIONS, TPM_HEADER_LEN},
    phy::TisPhy,
    xfer::Xfer,
};

/// Device family.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Family {
    /// 1.2: use the `tpm1` path.
    OneTwo,
    /// 2.0: use the root session/authorization path.
    TwoZero,
}
/// Property sub-item for probing: the total number of commands implemented by the device. Any such item
/// works — the probe only looks at the response tag, not the payload.
const PT_TOTAL_COMMANDS: u32 = 0x0000_0129;
/// Total length of the probe command: 10-byte header + three u32 payload words.
const PROBE_LEN: usize = TPM_HEADER_LEN + 12;
/// Scratch buffer for the probe response. It only reads the first two bytes (tag), so a header-sized
/// margin is enough.
const PROBE_RSP: usize = 64;
/// Determine the device family.
///
/// This borrows the link to send a single command and returns immediately; the link remains owned by the
/// caller for the subsequent boot sequence to take over. If the link is not in a send-ready state, it is
/// conservatively classified as 1.2 — do not enable the 2.0-specific path, even if it means admitting
/// less capability rather than misclassifying an unready device as 2.0 and running the authorization
/// handshake against it.
pub fn probe_family<P: TisPhy>(x: &mut Xfer<P>) -> Family {
    if !x.ready() {
        return Family::OneTwo;
    }
    let hdr = build_header(ST_NO_SESSIONS, CC_GET_CAPABILITY, PROBE_LEN as u32);
    let a = be32_bytes(CAP_TPM_PROPERTIES);
    let b = be32_bytes(PT_TOTAL_COMMANDS);
    let c = be32_bytes(1);
    let mut cmd = [0u8; PROBE_LEN];
    cmd[..TPM_HEADER_LEN].copy_from_slice(&hdr);
    cmd[TPM_HEADER_LEN] = a[0];
    cmd[TPM_HEADER_LEN + 1] = a[1];
    cmd[TPM_HEADER_LEN + 2] = a[2];
    cmd[TPM_HEADER_LEN + 3] = a[3];
    cmd[TPM_HEADER_LEN + 4] = b[0];
    cmd[TPM_HEADER_LEN + 5] = b[1];
    cmd[TPM_HEADER_LEN + 6] = b[2];
    cmd[TPM_HEADER_LEN + 7] = b[3];
    cmd[TPM_HEADER_LEN + 8] = c[0];
    cmd[TPM_HEADER_LEN + 9] = c[1];
    cmd[TPM_HEADER_LEN + 10] = c[2];
    cmd[TPM_HEADER_LEN + 11] = c[3];
    let mut rsp = [0u8; PROBE_RSP];
    match x.run(&cmd, PROBE_LEN, &mut rsp) {
        Ok((_n, _rc)) => {
            let tag = u16::from_be_bytes([rsp[0], rsp[1]]);
            if tag == ST_NO_SESSIONS {
                Family::TwoZero
            } else {
                Family::OneTwo
            }
        }
        Err(_) => Family::OneTwo,
    }
}
