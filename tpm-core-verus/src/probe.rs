use vstd::prelude::*;

use crate::cmd::{CAP_TPM_PROPERTIES, CC_GET_CAPABILITY};
use crate::cursor::be32_bytes;
use crate::msg::{build_header, ST_NO_SESSIONS, TPM_HEADER_LEN};
use crate::phy::TisPhy;
use crate::xfer::Xfer;

verus! {

// ===========================================================================
// Family probe
// ===========================================================================
//
// Whether the device follows 1.2 or 2.0 is found out with one command: send a capability query in a **2.0 frame**, then look only at the
// tag in the response header. A 2.0 device recognizes the tag and answers with the same set of tags; a 1.2 device does not and answers with a
// different tag. The return code is deliberately ignored -- whether the device likes the command does not matter; what matters is which set of
// tags it replies with.
//
// This layer sits across the protocol rules of the two families and is kernel glue (ring C): it is not part of the proof body, only
// declares its signature with `external_body`, treating the whole decision as a trusted implementation. The decision itself changes no proven
// property -- it only decides which boot sequence the link is handed to next.

/// Device family.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Family {
    /// 1.2: take the `tpm1` path.
    OneTwo,
    /// 2.0: take the root session/authorization path.
    TwoZero,
}

/// Property sub-item used for probing: the total number of commands the device implements. Which one is chosen does not matter -- the probe looks only at the response tag,
/// not the payload.
const PT_TOTAL_COMMANDS: u32 = 0x0000_0129;

/// Total probe command length: 10 header bytes + three u32 payload words.
const PROBE_LEN: usize = TPM_HEADER_LEN + 12;

/// Probe response scratch buffer. Only its first two bytes (the tag) are read; leaving header-sized slack is enough.
const PROBE_RSP: usize = 64;

/// Determine the device family.
///
/// Borrows the link to send one command and returns immediately; the link remains owned by the caller for the subsequent boot sequence to take over. If the link
/// is not in a state to send commands, conservatively classify as 1.2 -- i.e. do not enable the 2.0-only path; better to under-recognize capability
/// than to mistake a not-ready device for 2.0 and run the authorization handshake.
#[verifier::external_body]
pub fn probe_family<P: TisPhy>(x: &mut Xfer<P>) -> Family {
    if !x.ready() {
        return Family::OneTwo;
    }

    // 2.0 frame: tag ST_NO_SESSIONS, command code GetCapability.
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
            // Look only at the tag; ignore the return code.
            let tag = u16::from_be_bytes([rsp[0], rsp[1]]);
            if tag == ST_NO_SESSIONS {
                Family::TwoZero
            } else {
                Family::OneTwo
            }
        },
        // Not a single byte came back: conservatively classify as 1.2.
        Err(_) => Family::OneTwo,
    }
}

} // verus!
