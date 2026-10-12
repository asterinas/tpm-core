# tpm-core

`tpm-core` is the runtime-focused TPM 2.0 core crate extracted from the Asterinas TPM stack.

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
    let tis = Tis {
        phy: MyPhy,
        locality: 0,
        held: false,
    };
    Xfer::new(tis)
}
```

## Publishing Model in This Repository

- `tpm-core`: public crate intended for crates.io publishing.
- `tpm-core-verus`: internal verification crate, currently `publish = false`.

## Notes

This crate is `no_std`. Platform integration must provide correct MMIO/CRB access semantics and
proper synchronization around each TPM device instance.
