# tpm-core

`tpm-core` is the runtime-focused TPM 2.0 core crate extracted from the Asterinas TPM stack.

This crate is the runtime-oriented extraction of the Verus verified version in the branch tpm-core-verus of
https://github.com/asterinas/tpm-core.

This package is designed for normal Rust users who need TPM transport/session primitives without
requiring a Verus toolchain.

## MSRV

- Minimum Supported Rust Version (MSRV): `1.75`

## Features

- `runtime` (default)
  - Enables the normal runtime TPM core implementation.
  - This is the feature most users should use.

## Quick Start

Add the crate:

```toml
[dependencies]
tpm-core = "0.1"
```

If you are testing locally in this workspace:

```toml
[dependencies]
tpm-core = { path = "../tpm-core" }
```

## Example

A minimal skeleton for wiring your own TPM physical backend:

```rust
use tpm_core::{Tis, TisPhy, TisErr, Xfer};

struct MyPhy;

impl TisPhy for MyPhy {
    fn read8(&mut self, _addr: u32) -> Result<u8, TisErr> { unimplemented!() }
    fn read32(&mut self, _addr: u32) -> Result<u32, TisErr> { unimplemented!() }
    fn write8(&mut self, _addr: u32, _value: u8) -> Result<(), TisErr> { unimplemented!() }
    fn write32(&mut self, _addr: u32, _value: u32) -> Result<(), TisErr> { unimplemented!() }
    fn read_fifo(&mut self, _addr: u32, _out: &mut [u8], _off: usize, _n: usize) -> Result<(), TisErr> { unimplemented!() }
    fn write_fifo(&mut self, _addr: u32, _data: &[u8], _off: usize, _n: usize) -> Result<(), TisErr> { unimplemented!() }
    fn reset_fifo(&mut self, _addr: u32) {}
    fn delay(&mut self) {}
}

fn build_transport() -> Xfer<MyPhy> {
     let tis = Tis::new(MyPhy, 0);
    Xfer::new(tis)
}
```

## Notes

This crate is `no_std`. Platform integration must provide correct MMIO/CRB access semantics and
proper synchronization around each TPM device instance.

## Kernel/Platform Contract

To keep transport behavior safe and predictable, the kernel/platform side must satisfy these contracts:

1. Single-owner access per TPM instance.
    - Do not issue concurrent commands on the same TPM instance.
    - Serialize all accesses that share the same register/FIFO window.

2. Correct locality discipline.
    - Use a valid locality (`0..MAX_LOCALITY`).
    - Treat locality ownership as transport-internal state; do not modify it outside transport APIs.

3. Correct MMIO semantics.
    - `read32`/`write32` must map to TPM register accesses with the expected little-endian behavior.
    - MMIO failures must be reported as `Err(TisErr::Phy)` (or an equivalent `TisErr`) rather than ignored.

4. FIFO bounds discipline.
    - Callers/implementations must satisfy `off + n <= out.len()` for reads and `off + n <= data.len()` for writes.
    - Violating these bounds can panic in FIFO implementations.

5. Polling progress assumption.
    - `delay()` must eventually return and must not block forever.
    - Timeout behavior is modeled in polling counts, so each poll iteration must be able to make progress.

6. Buffer and framing contract.
    - Command buffers must carry a self-consistent TPM header length field.
    - Response buffers must be large enough to hold at least the response header and expected body.
