pub(crate) fn be16_of_exec(b0: u8, b1: u8) -> u16 {
    u16::from_be_bytes([b0, b1])
}
pub(crate) fn be32_of_exec(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    u32::from_be_bytes([b0, b1, b2, b3])
}
