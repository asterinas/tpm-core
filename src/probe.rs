use crate::{
    cmd::{CAP_TPM_PROPERTIES, CC_GET_CAPABILITY},
    cursor::be32_bytes,
    msg::{ST_NO_SESSIONS, TPM_HEADER_LEN, build_header},
    phy::TisPhy,
    xfer::Xfer,
};

/// 器件家族。
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Family {
    /// 1.2:走 `tpm1` 路径。
    OneTwo,
    /// 2.0:走根部的会话/授权路径。
    TwoZero,
}
/// 探测用的属性子项:器件实现的命令总数。取哪一项无所谓——探测只看响应标签,
/// 不看载荷。
const PT_TOTAL_COMMANDS: u32 = 0x0000_0129;
/// 探测命令总长:头 10 + 三个 u32 载荷。
const PROBE_LEN: usize = TPM_HEADER_LEN + 12;
/// 探测响应暂存区。只读它的前两个字节(标签),给足头部余量即可。
const PROBE_RSP: usize = 64;
/// 判定器件家族。
///
/// 借用链路发一条命令即返回,链路仍归调用方所有,供随后的引导序列接管。链路
/// 若不处于可发命令的状态,保守判为 1.2——即不启用 2.0 专属路径,宁可少认能力
/// 也不误把一个没准备好的器件当成 2.0 去跑授权握手。
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
