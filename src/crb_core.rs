use crate::{
    crb::*,
    crb_phy::{CrbPhy, check_cmd_bounds, check_rsp_bounds},
    cursor::Cursor,
    msg::TPM_HEADER_LEN,
};

// ===========================================================================
// 驱动状态
// ===========================================================================

pub struct Crb<P: CrbPhy> {
    pub phy: P,
    /// 本驱动使用的 locality 号。
    pub locality: u8,
    /// 是否已申请到 locality 且尚未归还。
    pub held: bool,
}

impl<P: CrbPhy> Crb<P> {
    #[inline]
    pub fn wf(&self) -> bool {
        self.locality < MAX_LOCALITY
    }

    #[inline]
    pub fn quiescent(&self) -> bool {
        !self.held
    }

    // =======================================================================
    // 通用轮询
    // =======================================================================

    /// 轮询一个控制区寄存器，直到 `(value & mask) == want`。
    fn wait_reg32(&mut self, reg: u32, mask: u32, want: u32, budget: u32) -> Result<u32, CrbErr> {
        let mut left = budget;
        while left > 0 {
            let v = self.phy.read32(reg)?;
            if (v & mask) == want {
                return Ok(v);
            }
            self.phy.delay();
            left -= 1;
        }
        Err(CrbErr::Timeout)
    }

    // =======================================================================
    // locality
    // =======================================================================

    pub fn request_locality(&mut self, budget: u32) -> Result<(), CrbErr> {
        self.phy.write32(REG_LOC_CTRL, LOC_CTRL_REQUEST)?;

        let want = LOC_STATE_ASSIGNED | LOC_STATE_VALID;
        self.wait_reg32(REG_LOC_STATE, want, want, budget)?;
        self.held = true;
        Ok(())
    }

    pub fn relinquish_locality(&mut self) {
        let _ = self.phy.write32(REG_LOC_CTRL, LOC_CTRL_RELINQUISH);
        self.held = false;
    }

    // =======================================================================
    // 就绪 / 空闲
    // =======================================================================

    fn cmd_ready(&mut self, budget: u32) -> Result<(), CrbErr> {
        self.phy.write32(REG_CTRL_REQ, CTRL_REQ_CMD_READY)?;
        self.wait_reg32(REG_CTRL_REQ, CTRL_REQ_CMD_READY, 0, budget)?;
        Ok(())
    }

    fn go_idle(&mut self, budget: u32) -> Result<(), CrbErr> {
        self.phy.write32(REG_CTRL_REQ, CTRL_REQ_GO_IDLE)?;
        self.wait_reg32(REG_CTRL_REQ, CTRL_REQ_GO_IDLE, 0, budget)?;
        Ok(())
    }

    // =======================================================================
    // 发送
    // =======================================================================

    pub fn send(&mut self, cmd: &[u8], len: usize) -> Result<(), CrbErr> {
        if len == 0 {
            return Err(CrbErr::BadLength);
        }
        check_cmd_bounds(cmd, len)?;

        // 清取消位，避免本次命令被上一次残留取消请求影响。
        self.phy.write32(REG_CTRL_CANCEL, CTRL_CANCEL_CLEAR)?;

        // 设备上报的可用命令大小复核。
        let adv = self.phy.read32(REG_CTRL_CMD_SIZE)?;
        if (len as u32) > adv {
            return Err(CrbErr::BadLength);
        }

        self.phy.write_cmd(cmd, len)?;

        // 确保缓冲写入先于 START 对设备可见。
        self.phy.fence();

        self.phy.write32(REG_CTRL_START, CTRL_START_INVOKE)
    }

    // =======================================================================
    // 完成 / 接收
    // =======================================================================

    fn wait_complete(&mut self, budget: u32) -> Result<(), CrbErr> {
        self.wait_reg32(REG_CTRL_START, CTRL_START_INVOKE, 0, budget)?;
        Ok(())
    }

    pub fn recv(&mut self, out: &mut [u8]) -> Result<usize, CrbErr> {
        if out.len() < TPM_HEADER_LEN {
            return Err(CrbErr::BadLength);
        }

        let sts = self.phy.read32(REG_CTRL_STS)?;
        if (sts & CTRL_STS_ERROR) != 0 {
            return Err(CrbErr::Protocol);
        }

        check_rsp_bounds(0, out.len(), TPM_HEADER_LEN)?;

        self.phy.read_rsp(0, out, TPM_HEADER_LEN)?;

        let mut c = Cursor::at(2);
        let expected = c.read_be32(out).ok_or(CrbErr::BadLength)?;
        let n = expected as usize;

        if n < TPM_HEADER_LEN {
            return Err(CrbErr::BadLength);
        }
        check_rsp_bounds(0, out.len(), n)?;

        self.phy.read_rsp(TPM_HEADER_LEN, out, n - TPM_HEADER_LEN)?;

        // 与原规约等价的运行时保护：响应长度字段应与返回长度一致。
        let hdr_len = u32::from_be_bytes([out[2], out[3], out[4], out[5]]) as usize;
        if hdr_len != n {
            return Err(CrbErr::BadLength);
        }

        Ok(n)
    }

    // =======================================================================
    // 一次完整往返
    // =======================================================================

    pub fn transmit(&mut self, cmd: &[u8], len: usize, out: &mut [u8]) -> Result<usize, CrbErr> {
        if !self.wf()
            || !self.quiescent()
            || len < TPM_HEADER_LEN
            || len > cmd.len()
            || out.len() < TPM_HEADER_LEN
        {
            return Err(CrbErr::BadLength);
        }

        self.request_locality(budget_of(TIMEOUT_C_MS))?;
        let res = self.exchange(cmd, len, out);
        self.relinquish_locality();
        res
    }

    fn exchange(&mut self, cmd: &[u8], len: usize, out: &mut [u8]) -> Result<usize, CrbErr> {
        self.cmd_ready(budget_of(TIMEOUT_C_MS))?;
        self.send(cmd, len)?;
        self.wait_complete(budget_of(TIMEOUT_LONG_MS))?;

        let n = self.recv(out)?;

        // 收尾失败不覆盖已得到的响应。
        let _ = self.go_idle(budget_of(TIMEOUT_C_MS));
        Ok(n)
    }
}
