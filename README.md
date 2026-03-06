# FrozenCore

Custom implementations and core utilities for frozen codebases.

## Index

- [`usage`](#usage)
- [`ffile`](#frozenfile)
- [`fmmap`](#frozenmmap)
- [`error`](#frozenerr)
- [`hints`](#hints)
- [`crc32`](#crc32)
- [`bpool`](#bpool)
- [`notes`](#notes)

## Usage

Add following to your `Cargo.toml`,

```toml
[dependencies]
frozen-core = { version = "0.0.9", default-features = true }
```

> [!TIP]
> All the features available by default. To disable this, set `default-features = false`

## FrozenFile

`FrozenFile` is a custom implementation of `std::fs::File`.

To use the `ffile` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.9", default-features = false, features = ["ffile"] }
```

`FrozenFile` is currently available on the following platforms,

| Platform                              | Support |
|---------------------------------------|:-------:|
| `aarch64-unknown-linux-gnu`           | ✅      |
| `x86_64-unknown-linux-gnu`            | ✅      |
| `aarch64-pc-windows-msvc`             | ❌      |
| `x86_64-pc-windows-msvc`              | ❌      |
| `aarch64-apple-darwin`                | ✅      |
| `x86_64-apple-darwin`                 | ✅      |

See following [example](./examples/ff.rs) for more details.

## FrozenMMap

`FrozenMMap` is a custom implementation of `mmap`.

To use the `fmmap` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.9", default-features = false, features = ["fmmap"] }
```

`FrozenMMap` is currently available on the following platforms,

| Platform                              | Support |
|---------------------------------------|:-------:|
| `aarch64-unknown-linux-gnu`           | ✅      |
| `x86_64-unknown-linux-gnu`            | ✅      |
| `aarch64-pc-windows-msvc`             | ❌      |
| `x86_64-pc-windows-msvc`              | ❌      |
| `aarch64-apple-darwin`                | ✅      |
| `x86_64-apple-darwin`                 | ✅      |

Read the example below for usage details,

```rs
use frozen_core::fmmap::{FMCfg, FrozenMMap};

const MID: u8 = 0;

#[repr(C)]
#[derive(Debug)]
struct Meta(u64);

unsafe impl Send for Meta {}
unsafe impl Sync for Meta {}

fn main() {
    let dir = std::path::PathBuf::from("./target/examples");
    let path = dir.join("fm_example.bin");

    let _ = std::fs::remove_file(&path);
    std::fs::create_dir_all(&dir).unwrap();

    let cfg = FMCfg {
        mid: MID,
        initial_count: 1,
        path: path.clone(),
        flush_duration: std::time::Duration::from_micros(100),
    };

    let mmap = FrozenMMap::<Meta>::new(cfg.clone()).unwrap();
    assert_eq!(mmap.slots(), 1);

    let (_, epoch) = mmap.write(0, |m| m.0 = 0x0A).unwrap();
    mmap.wait_for_durability(epoch).unwrap();

    let val = mmap.read(0, |m| m.0).unwrap();
    assert_eq!(val, 10);

    mmap.grow(1).unwrap();
    assert_eq!(mmap.slots(), 2);

    mmap.write(1, |m| m.0 = 0x0F).unwrap();
    drop(mmap); // syncs data

    // reopen & verify
    let reopened = FrozenMMap::<Meta>::new(cfg).unwrap();

    let v0 = reopened.read(0, |m| m.0).unwrap();
    let v1 = reopened.read(1, |m| m.0).unwrap();

    assert_eq!(v0, 0x0A);
    assert_eq!(v1, 0x0F);
}
```

## FrozenErr

`FRes` & `FErr` are custom implementation's for result and error propogation.

To use the `error` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.9", default-features = false, features = ["error"] }
```

## Hints

The `hints` module provides stable friendly implementations of `likely` and `unlikely` branch hints functions.

To use the `hints` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.9", default-features = false, features = ["hints"] }
```

## Crc32

Implementation of CRC32C (Castagnoli polynomial) to compute a 32-bit cyclic redundancy check (CRC) using
Castagnoli polynomial, intended for data integrity verification for torn writes and curruption detection

> [!WARNING]
> We assume little-endian target architecture, as big-endian architectures are not supported

> [!IMPORTANT]
> The generated 32-bit CRC is not cryptographically secure, it's intended use only is for data integrity in IO ops

To use the `crc32` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.9", default-features = false, features = ["crc32"] }
```

`Crc32C` is available on following architectires,

| Architecture    | Support |
|-----------------|:-------:|
| `aarch64`       | ✅      |
| `x86_64`        | ✅      |

Read the example below for usage details,

```rs
use frozen_core::crc32::Crc32C;

fn main() {
    let crc = Crc32C::new();

    let b0: [u8; 8] = *b"12345678";
    let b1: [u8; 8] = *b"ABCDEFGH";
    let b2: [u8; 8] = *b"abcdefgh";
    let b3: [u8; 8] = *b"zyxwvuts";

    assert_eq!(crc.crc(&b0), crc.crc(&b0));
    assert_eq!(crc.crc_2x([&b0, &b1]), crc.crc_2x([&b0, &b1]));
    assert_eq!(crc.crc_4x([&b0, &b1, &b2, &b3]), crc.crc_4x([&b0, &b1, &b2, &b3]));
}
```

## BPool

Lock-free buffer pool used for staging IO buffers

## Features

- *RAII Safe*
- *Graceful Shutdown*
- *Lock-free fast path*

## Pooling for allocations

Bufs are allocated in batches using `BPool::allocate`, it may allocate fewer than requested, in such cases
caller should wait using `BPool::wait` which block till any bufs are available to use again

To use the `bpool` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.9", default-features = false, features = ["bpool"] }
```

Read the example below for usage details,

```rs
use std::thread;
use std::sync::Arc;
use frozen_core::bpool::BPool;

const MODULE_ID: u8 = 0;
const CAPACITY: usize = 8;
const BUF_SIZE: usize = 0x20;

let pool = Arc::new(BPool::new(BUF_SIZE, CAPACITY, MODULE_ID));

let mut handles = Vec::new();
for _ in 0..4 {
    let pool = pool.clone();
    
    handles.push(thread::spawn(move || {
        for _ in 0..0x80 {
            let mut n = 2;
            while n != 0 {
                let alloc = pool.allocate(n);
                
                // pool when not all bufs are allocated
                if alloc.count == 0 {
                    pool.wait().expect("wait failed");
                    continue;
                }
                
               n -= alloc.count;
            }
            
            // NOTE: allocated bufs are freed automatically when `alloc` drops
        }
    }));
}

for h in handles {
    h.join().unwrap();
}
```

## Notes

> [!IMPORTANT]
> `frozen-core` is primarily created for [frozen-lab](https://github.com/frozen-lab/) projects.
> External use is discouraged, but not prohibited, given __you asume all the risks__.

This project is licensed under the Apache-2.0 and MIT License. 
See the [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT) file for more details.

Contributions are welcome! Please feel free to submit a PR or open an issue if you have any feedback or suggestions.
