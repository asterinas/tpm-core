use vstd::prelude::*;

use crate::phy::TisPhy;
use crate::tis::TisErr;

verus! {

pub assume_specification [u32::from_le] (_0: u32) -> u32;
pub assume_specification [u32::to_le] (_0: u32) -> u32;
pub assume_specification [core::hint::spin_loop] ();

// ===========================================================================
// Ring B: grounding the trusted spec
// ===========================================================================
//
// The core layer no longer holds raw pointers directly, nor depends on any platform MMIO library. It now uses a "safe backend":
// a concrete platform implements register read/write capability as `TisMmioBackend`, which this type wraps into a `TisPhy`.
// This keeps unsafe code out of the core side, leaving platform details entirely in ring C / the HAL.

// ---------------------------------------------------------------------------
// Safe backend interface
// ---------------------------------------------------------------------------

pub trait TisMmioBackend {
    fn read8(&mut self, addr: u32) -> Result<u8, TisErr>;

    fn read32(&mut self, addr: u32) -> Result<u32, TisErr>;

    fn write8(&mut self, addr: u32, value: u8) -> Result<(), TisErr>;

    fn write32(&mut self, addr: u32, value: u32) -> Result<(), TisErr>;
}

// ---------------------------------------------------------------------------
// Register window (backend adapter)
// ---------------------------------------------------------------------------

pub struct TisMmio<B: TisMmioBackend> {
    backend: B,
    /// Number of spin iterations per [`TisPhy::delay`]. Not a duration; the real interval depends on the target CPU frequency.
    spin: u32,
    /// Ghost accumulator referenced by the specs in `phy.rs`. Zero runtime overhead.
    ghost written: Seq<u8>,
}

impl<B: TisMmioBackend> TisMmio<B> {
    #[verifier::external_body]
    pub fn new(backend: B, spin: u32) -> (r: Self)
        ensures
            r.fifo_written() =~= Seq::<u8>::empty(),
    {
        TisMmio { backend, spin, written: Seq::empty() }
    }
}

impl<B: TisMmioBackend> TisPhy for TisMmio<B> {
    closed spec fn fifo_written(&self) -> Seq<u8> {
        self.written
    }

    // -----------------------------------------------------------------------
    // Registers
    // -----------------------------------------------------------------------

    #[verifier::external_body]
    fn read8(&mut self, addr: u32) -> (r: Result<u8, TisErr>) {
        self.backend.read8(addr)
    }

    #[verifier::external_body]
    fn read32(&mut self, addr: u32) -> (r: Result<u32, TisErr>) {
        let v = self.backend.read32(addr)?;
        Ok(u32::from_le(v))
    }

    #[verifier::external_body]
    fn write8(&mut self, addr: u32, value: u8) -> (r: Result<(), TisErr>) {
        self.backend.write8(addr, value)
    }

    #[verifier::external_body]
    fn write32(&mut self, addr: u32, value: u32) -> (r: Result<(), TisErr>) {
        self.backend.write32(addr, value.to_le())
    }

    // -----------------------------------------------------------------------
    // Data port
    // -----------------------------------------------------------------------

    #[verifier::external_body]
    fn read_fifo(&mut self, addr: u32, out: &mut [u8], off: usize, n: usize) -> (r: Result<
        (),
        TisErr,
    >) {
        for slot in &mut out[off..off + n] {
            *slot = self.backend.read8(addr)?;
        }
        Ok(())
    }

    #[verifier::external_body]
    fn write_fifo(&mut self, addr: u32, data: &[u8], off: usize, n: usize) -> (r: Result<
        (),
        TisErr,
    >) {
        for &byte in &data[off..off + n] {
            self.backend.write8(addr, byte)?;
        }
        Ok(())
    }

    /// Write `TPM_STS_COMMAND_READY` (0x40).
    #[verifier::external_body]
    fn reset_fifo(&mut self, addr: u32) {
        let _ = self.backend.write8(addr, 0x40u8);
        proof {
            self.written = self.written.subrange(0, 0);
        }
    }

    // -----------------------------------------------------------------------
    // Throttling
    // -----------------------------------------------------------------------

    #[verifier::external_body]
    fn delay(&mut self) {
        for _ in 0..self.spin {
            core::hint::spin_loop();
        }
    }
}

} // verus!
