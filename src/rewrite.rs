use super::{handle::*, table::SpaceTable};

/// 报文头长度：标签 2 字节 + 长度 4 字节 + 命令码或返回码 4 字节。
pub const HEADER_SIZE: usize = 10;
/// 命令句柄数由 3 位字段给出，上限为 7。
pub const MAX_CHANDLES: usize = 7;
pub const RC_SUCCESS: u32 = 0;
/// 能力查询里「句柄列表」这一类目。
pub const CAP_HANDLES: u32 = 0x0000_0001;
/// 能力响应体布局：更多数据标志 1 字节，类目 4 字节，数量 4 字节。
pub const CAP_MORE_OFF: usize = HEADER_SIZE;
const CAP_CAPABILITY_OFF: usize = HEADER_SIZE + 1;
const CAP_COUNT_OFF: usize = HEADER_SIZE + 5;
const CAP_HANDLES_OFF: usize = HEADER_SIZE + 9;
const RSP_LENGTH_OFF: usize = 2;
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SpaceErr {
    /// 报文长度与其自身声明的结构不符。
    Malformed,
    /// 命令引用了一个解析不出来的虚拟句柄。
    BadHandle,
}
pub fn read_be32(b: &[u8], off: usize) -> u32 {
    u32::from_be_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]])
}
fn write_be32(b: &mut [u8], off: usize, v: u32) {
    b[off..off + 4].copy_from_slice(&v.to_be_bytes());
}
/// 把命令句柄区里的虚拟句柄换成物理句柄。
///
/// `nr_handles` 由命令码的属性表给出，属于阶段 2 的编解码产物；这里只
/// 把它当成一个已经过校验的参数。
pub fn map_command_handles(
    tbl: &SpaceTable,
    nr_handles: usize,
    cmd: &mut [u8],
) -> Result<(), SpaceErr> {
    for i in 0..nr_handles {
        let h = read_be32(cmd, HEADER_SIZE + 4 * i);
        if is_transient_exec(h) && tbl.resolve(h).is_none() {
            return Err(SpaceErr::BadHandle);
        }
    }
    for i in 0..nr_handles {
        let h = read_be32(cmd, HEADER_SIZE + 4 * i);
        if is_transient_exec(h) {
            let p = tbl.resolve(h).unwrap();
            write_be32(cmd, HEADER_SIZE + 4 * i, p);
        }
    }
    Ok(())
}
/// 响应头句柄的处理结果。
///
/// `OutOfSlots` 把「必须释放这个物理句柄」这条义务写进了返回值类型，
/// 而不是留给调用方凭约定记住。编排层不处理它就编译不过。
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum HeaderOutcome {
    /// 响应里没有句柄，或命令本身失败，报文未改动。
    NoHandle,
    /// 瞬态句柄已替换为虚拟句柄。
    Virtualized { vhandle: u32 },
    /// 会话句柄已登记，报文未改动（会话句柄不虚拟化）。
    SessionTracked { phandle: u32 },
    /// 句柄类型不认识，报文未改动。
    Unknown { phandle: u32 },
    /// 表已满，必须释放 `flush`。
    OutOfSlots { flush: u32 },
}
/// 处理响应头部返回的句柄。
pub fn map_response_handle(
    tbl: &mut SpaceTable,
    has_rhandle: bool,
    rsp: &mut [u8],
) -> HeaderOutcome {
    if !has_rhandle {
        return HeaderOutcome::NoHandle;
    }
    let rc = read_be32(rsp, 6);
    if rc != RC_SUCCESS {
        return HeaderOutcome::NoHandle;
    }
    let phandle = read_be32(rsp, HEADER_SIZE);
    if is_transient_exec(phandle) {
        if phandle == 0 || phandle == CTX_SAVED_SENTINEL || tbl.lookup(phandle).is_some() {
            return HeaderOutcome::OutOfSlots { flush: phandle };
        }
        match tbl.intern(phandle) {
            Some(vhandle) => {
                write_be32(rsp, HEADER_SIZE, vhandle);
                HeaderOutcome::Virtualized { vhandle }
            }
            None => HeaderOutcome::OutOfSlots { flush: phandle },
        }
    } else if is_session_exec(phandle) {
        if phandle == 0 || tbl.has_session_exec(phandle) {
            return HeaderOutcome::OutOfSlots { flush: phandle };
        }
        if tbl.add_session(phandle) {
            HeaderOutcome::SessionTracked { phandle }
        } else {
            HeaderOutcome::OutOfSlots { flush: phandle }
        }
    } else {
        HeaderOutcome::Unknown { phandle }
    }
}
/// 改写能力查询响应里的句柄列表：瞬态句柄换成虚拟句柄，本 space 不认识的
/// 瞬态句柄**从列表中剔除**，其余原样保留。列表就地压紧，长度字段与
/// 数量字段一并更新。
///
/// 剔除是隔离性的直接体现：一个 space 枚举瞬态对象时，只应看见自己的。
///
/// 返回改写后的报文总长度。
pub fn map_capability_handles(
    tbl: &SpaceTable,
    is_cap_query: bool,
    rsp: &mut [u8],
    len: usize,
) -> Result<usize, SpaceErr> {
    if !is_cap_query {
        return Ok(len);
    }
    if len < CAP_HANDLES_OFF {
        return Err(SpaceErr::Malformed);
    }
    let rc = read_be32(rsp, 6);
    if rc != RC_SUCCESS {
        return Ok(len);
    }
    if read_be32(rsp, CAP_CAPABILITY_OFF) != CAP_HANDLES {
        return Ok(len);
    }
    let tail = len - CAP_HANDLES_OFF;
    if !tail.is_multiple_of(4) {
        return Err(SpaceErr::Malformed);
    }
    let avail: usize = tail / 4;
    let declared = read_be32(rsp, CAP_COUNT_OFF);
    if declared as usize != avail {
        return Err(SpaceErr::Malformed);
    }
    let count: usize = avail;
    let mut j: usize = 0;
    for i in 0..count {
        let h = read_be32(rsp, CAP_HANDLES_OFF + 4 * i);
        if is_transient_exec(h) {
            if h != 0 && h != CTX_SAVED_SENTINEL {
                if let Some(v) = tbl.lookup(h) {
                    write_be32(rsp, CAP_HANDLES_OFF + 4 * j, v);
                    j += 1;
                }
            }
        } else {
            write_be32(rsp, CAP_HANDLES_OFF + 4 * j, h);
            j += 1;
        }
    }
    let new_len = CAP_HANDLES_OFF + 4 * j;
    write_be32(rsp, CAP_COUNT_OFF, j as u32);
    write_be32(rsp, RSP_LENGTH_OFF, new_len as u32);
    Ok(new_len)
}
