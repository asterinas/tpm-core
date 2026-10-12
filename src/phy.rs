use crate::tis::TisErr;

pub trait TisPhy {
    fn read8(&mut self, addr: u32) -> Result<u8, TisErr>;
    fn read32(&mut self, addr: u32) -> Result<u32, TisErr>;
    fn write8(&mut self, addr: u32, value: u8) -> Result<(), TisErr>;
    fn write32(&mut self, addr: u32, value: u32) -> Result<(), TisErr>;
    /// 从数据口取 `n` 字节，落到 `out[off..off + n]`。
    ///
    /// 取到的内容是器件给的，规约里说不出它是什么，只能保证**落点正确**：
    /// 区间之外一字未动，缓冲区长度不变。防越界的责任因此完全落在调用方给出
    /// 的 `off + n <= out.len()` 上，而这一条由类型检查强制。
    fn read_fifo(&mut self, addr: u32, out: &mut [u8], off: usize, n: usize) -> Result<(), TisErr>;
    /// 把 `data[off..off + n]` 写进数据口。
    ///
    /// 失败时器件可能已经吃进了一段前缀——总线传输不是原子的。规约如实写成
    /// 「累积量只增不减」而不是「原封不动」：后者是假的，写成假的会让基于它的
    /// 推理全部无效。调用方在任何失败路径上都必须复位数据口，复位之后这点不
    /// 精确就无关紧要了。
    fn write_fifo(&mut self, addr: u32, data: &[u8], off: usize, n: usize) -> Result<(), TisErr>;
    /// 中止当前命令并清空数据口。
    ///
    /// 对应写入「命令就绪」位。它既是发送前的准备动作，也是所有错误路径的收尾
    /// 动作——半条命令留在器件里，比什么都没写更危险。
    ///
    /// 没有返回值：复位失败无从补救，而调用点全在错误处理路径上，多一个要处理
    /// 的错误只会让那些路径更容易写漏。
    fn reset_fifo(&mut self, addr: u32);
    /// 两次轮询之间的等待。
    ///
    /// 时长由实现决定，规约里不出现——本层的超时是用轮询次数表达的，等待多久
    /// 只影响真实耗时，不影响任何一条被证明的性质。
    fn delay(&mut self);
}
