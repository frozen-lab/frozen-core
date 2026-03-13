[![License](https://img.shields.io/github/license/frozen-lab/frozen_core?logo=open-source-initiative&logoColor=white)](https://github.com/frozen-lab/frozen_core/blob/master/LICENSE)
[![Latest Version](https://img.shields.io/crates/v/frozen_core.svg)](https://crates.io/crates/frozen_core)
[![Tests](https://github.com/frozen-lab/frozen_core/actions/workflows/tests.yaml/badge.svg)](https://github.com/frozen-lab/frozen_core/actions/workflows/tests.yaml)
[![Pull Requests](https://img.shields.io/github/issues-pr/frozen-lab/frozen_core?logo=github&logoColor=white)](https://github.com/frozen-lab/frozen_core/pulls)
[![GitHub Issues or Pull Requests](https://img.shields.io/github/issues/frozen-lab/frozen_core?logo=github&logoColor=white)](https://github.com/frozen-lab/frozen_core/issues)

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
- [`mpscq`](#mpscq)
- [`fpipe`](#frozenpipe)
- [`notes`](#notes)

## Usage

Add following to your `Cargo.toml`,

```toml
[dependencies]
frozen-core = { version = "0.0.12", default-features = true }
```

> [!TIP]
> All the features are enabled by default. To disable this, set `default-features = false`

## FrozenFile

`FrozenFile` is a custom implementation of `std::fs::File`.

To use the `ffile` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.12", default-features = false, features = ["ffile"] }
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
frozen-core = { version = "0.0.12", default-features = false, features = ["fmmap"] }
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

`FRes` & `FErr` are custom implementation's for result and error propagation.

To use the `error` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.12", default-features = false, features = ["error"] }
```

## Hints

The `hints` module provides stable friendly implementations of `likely` and `unlikely` branch hints functions.

To use the `hints` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.12", default-features = false, features = ["hints"] }
```

## Crc32

Implementation of CRC32C (Castagnoli polynomial) to compute a 32-bit cyclic redundancy check (CRC) using
Castagnoli polynomial, intended for data integrity verification for torn writes and corruption detection

> [!WARNING]
> We assume little-endian target architecture, as big-endian architectures are not supported

> [!IMPORTANT]
> The generated 32-bit CRC is not cryptographically secure, it's intended use only is for data integrity in IO ops

To use the `crc32` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.12", default-features = false, features = ["crc32"] }
```

`Crc32C` is available on following architectures,

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

To use the `bpool` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.12", default-features = false, features = ["bpool"] }
```

Read the example below for usage details,

```rs
use frozen_core::bpool::{BPBackend, BPCfg, BufPool};
use std::sync::Arc;
use std::thread;

fn main() {
    let pool = Arc::new(BufPool::new(BPCfg {
        mid: 0,
        chunk_size: 0x20,
        backend: BPBackend::Prealloc { capacity: 0x10 },
    }));

    let mut threads = Vec::new();
    for _ in 0..4 {
        let pool = pool.clone();

        threads.push(thread::spawn(move || {
            for _ in 0..0x80 {
                let alloc = pool.allocate(4).expect("allocation failed");
                assert_eq!(alloc.count, 4);
            }
        }));
    }

    for t in threads {
        t.join().expect("thread failed");
    }
}
```

## MPSCQ

A lock-free multi-producer single-consumer queue

To use the `mpscq` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.12", default-features = false, features = ["mpscq"] }
```

Read the example below for usage details,

```rs
use frozen_core::mpscq::MPSCQueue;

fn main() {
    let queue = MPSCQueue::<usize>::default();

    queue.push(1usize);
    queue.push(2usize);
    queue.push(3usize);

    let batch = queue.drain();

    assert_eq!(batch.len(), 3);
    assert_eq!(batch, vec![3usize, 2usize, 1usize]);

    drop(batch); // values is dropped here
}
```

## FrozenPipe

An high throughput asynchronous IO pipeline for chunk based storage, it uses batches to write requests and
flushes them in the background, while providing durability guarantees via epochs

To use the `fpipe` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.12", default-features = false, features = ["fpipe"] }
```

Read the example below for usage details,

```rs
use frozen_core::bpool::{BPBackend, BPCfg, BufPool};
use frozen_core::ffile::{FFCfg, FrozenFile};
use frozen_core::fpipe::FrozenPipe;
use std::time::Duration;

fn main() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("tmp_pipe");

    let file = FrozenFile::new(FFCfg {
        path,
        mid: 0,
        chunk_size: 0x20,
        initial_chunk_amount: 4,
    })
    .unwrap();

    let pool = BufPool::new(BPCfg {
        mid: 0,
        chunk_size: 0x20,
        backend: BPBackend::Prealloc { capacity: 0x10 },
    });

    let pipe = FrozenPipe::new(file, pool, Duration::from_micros(0x3A)).unwrap();

    let buf = vec![1u8; 0x40];
    let epoch = pipe.write(&buf, 0).unwrap();

    pipe.wait_for_durability(epoch).unwrap();

    let read = pipe.read(0, 2).unwrap();
    assert_eq!(read, buf);
}
```

## Notes

> [!IMPORTANT]
> `frozen-core` is primarily created for [frozen-lab](https://github.com/frozen-lab/) projects.
> External use is discouraged, but not prohibited, given __you assume all the risks__.

This project is licensed under the Apache-2.0 and MIT License. 
See the [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT) file for more details.

Contributions are welcome! Please feel free to submit a PR or open an issue if you have any feedback or suggestions.
