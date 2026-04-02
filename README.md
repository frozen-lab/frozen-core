[![Latest Version](https://img.shields.io/crates/v/frozen_core.svg)](https://crates.io/crates/frozen_core)
[![License](https://img.shields.io/github/license/frozen-lab/frozen_core?logo=open-source-initiative&logoColor=white)](https://github.com/frozen-lab/frozen_core/blob/master/LICENSE)
[![Tests](https://github.com/frozen-lab/frozen_core/actions/workflows/tests.yaml/badge.svg)](https://github.com/frozen-lab/frozen_core/actions/workflows/tests.yaml)

# FrozenCore

Custom implementations and core utilities for [frozen-lab](https://github.com/frozen-lab/) crates.

## Index

- [`notes`](#notes)
- [`error`](#frozenerr)
- [`hints`](#hints)
- [`ffile`](#frozenfile)
- [`fmmap`](#frozenmmap)
- [`crc32`](#crc32)
- [`bpool`](#bpool)
- [`mpscq`](#mpscq)
- [`fpipe`](#frozenpipe)

## Notes

> [!IMPORTANT]
> `frozen-core` is primarily created for [frozen-lab](https://github.com/frozen-lab/) projects. External use is
> discouraged, but not prohibited, given __you assume all the risks__.

This project is licensed under the Apache-2.0 and MIT License. See the [LICENSE-APACHE](LICENSE-APACHE) and
[LICENSE-MIT](LICENSE-MIT) file for more details.

Contributions are welcome! Please feel free to submit a PR or open an issue if you have any feedback or suggestions.

> [!NOTE]
> `frozen-core` contains next to naught AI-generated code. Therefore, any catastrophic bugs or fatal crashes encountered
> are results of pure & unadulterated skill issues

## FrozenErr

`FrozenRes` & `FrozenErr` are custom implementation's for result and error propagation.

To use the `error` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.17", features = ["error"] }
```

## Hints

The `hints` module provides stable friendly implementations of `likely` and `unlikely` branch hints functions.

To use the `hints` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.17", features = ["hints"] }
```

## FrozenFile

`FrozenFile` is a custom implementation of `std::fs::File`.

To use the `ffile` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.17", features = ["ffile"] }
```

`FrozenFile` is currently available on the following platforms,

| Platform                              | Support |
|:--------------------------------------|:--------|
| `aarch64-unknown-linux-gnu`           | ✅      |
| `x86_64-unknown-linux-gnu`            | ✅      |
| `aarch64-pc-windows-msvc`             | ❌      |
| `x86_64-pc-windows-msvc`              | ❌      |
| `aarch64-apple-darwin`                | ✅      |
| `x86_64-apple-darwin`                 | ✅      |

## FrozenMMap

`FrozenMMap` is a custom implementation of `mmap`.

To use the `fmmap` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.17", features = ["fmmap"] }
```

`FrozenMMap` is currently available on the following platforms,

| Platform                              | Support |
|:--------------------------------------|:--------|
| `aarch64-unknown-linux-gnu`           | ✅      |
| `x86_64-unknown-linux-gnu`            | ✅      |
| `aarch64-pc-windows-msvc`             | ❌      |
| `x86_64-pc-windows-msvc`              | ❌      |
| `aarch64-apple-darwin`                | ✅      |
| `x86_64-apple-darwin`                 | ✅      |

## Crc32

Implementation of CRC32C (Castagnoli polynomial) to compute a 32-bit cyclic redundancy check (CRC) using Castagnoli
polynomial, intended for data integrity verification for torn writes and corruption detection.

> [!WARNING]
> We assume little-endian target architecture, as big-endian architectures are not supported

> [!IMPORTANT]
> The generated 32-bit CRC is not cryptographically secure, it's intended use only is for data integrity in IO ops

To use the `crc32` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.17", features = ["crc32"] }
```

`Crc32C` is available on following architectures,

| Architecture    | Support |
|:----------------|:--------|
| `aarch64`       | ✅      |
| `x86_64`        | ✅      |

Look at following benches for the throughout and latency measurements,

| Mode | Size    | Time (ns / µs)        | Throughput (GiB/s) |
|:-----|:--------|:----------------------|:-------------------|
| 1x   | 4 KiB   | 318 ns                | 11.97              |
| 2x   | 4 KiB   | 340 ns                | 11.24              |
| 4x   | 4 KiB   | 451 ns                | 8.46               |
| 1x   | 64 KiB  | 5.44 µs               | 11.23              |
| 2x   | 64 KiB  | 5.26 µs               | 11.60              |
| 4x   | 64 KiB  | 7.50 µs               | 8.14               |
| 1x   | 1 MiB   | 89.80 µs              | 10.88              |
| 2x   | 1 MiB   | 90.56 µs              | 10.78              |
| 4x   | 1 MiB   | 120.04 µs             | 8.13               |

Environment used for benching,

- OS: NixOS (WSL2)
- Architecture: x86_64
- Memory: 8 GiB RAM (DDR4)
- Backend: Hardware (SSE4.2)
- Rust: rustc 1.86.0 w/ cargo 1.86.0
- Kernel: Linux 6.6.87.2-microsoft-standard-WSL2
- CPU: Intel® Core™ i5-10300H @ 2.50GHz (4C / 8T)

## BPool

Lock-free buffer pool used for staging IO buffers.

It offers following backends,

- **Dynamic:** fastest, low latency, heap allocated
- **Prealloc:** stable under contention, bounded memory, lock free reuse

To use the `bpool` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.17", features = ["bpool"] }
```

Following are latency measurements for allocation across different backends and configurations.

> [!NOTE]
> All timings represent **allocation + drop (RAII lifecycle)**

Single tx latency,

| N (Chunks) |  Dynamic Time (ns / µs) | Prealloc Time (ns / µs) |
|:-----------|:------------------------|:------------------------|
| 1          | 150 ns                  | 262 ns                  |
| 4          | 163 ns                  | 595 ns                  |
| 16         | 163 ns                  | 1.97 µs                 |
| 64         | 220 ns                  | 8.25 µs                 |

Prealloc scaling (batch size),

| N (chunks) | Time (ns / µs) |
|:-----------|:---------------|
| 1          | 253 ns         |
| 8          | 1.13 µs        |
| 32         | 3.97 µs        |
| 128        | 14.84 µs       |

Contention (multi tx),

| Threads | Time (µs) |
|:--------|:----------|
|       2 |    132 µs |
|       4 |    243 µs |
|       8 |    519 µs |

Blocking behavior (Prealloc),

| Scenario        | Time (µs) |
|:----------------|:----------|
| Pool exhaustion |   68.6 µs |

Fallback (Prealloc -> Dynamic),

| N (chunks) | Time (ns) |
|:-----------|:----------|
| 32         | 201 ns    |
| 64         | 229 ns    |
| 128        | 252 ns    |

Where value of `N` is `N = 64`.

Environment used for benching,

- OS: NixOS (WSL2)
- Architecture: x86_64
- Memory: 8 GiB RAM (DDR4)
- Rust: rustc 1.86.0 w/ cargo 1.86.0
- Kernel: Linux 6.6.87.2-microsoft-standard-WSL2
- CPU: Intel® Core™ i5-10300H @ 2.50GHz (4C / 8T)

## MPSCQ

A lock-free multi-producer single-consumer queue.

To use the `mpscq` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.17", features = ["mpscq"] }
```

## FrozenPipe

An high throughput asynchronous IO pipeline for chunk based storage, it uses batches to write requests and flushes
them in the background, while providing durability guarantees via epochs.

To use the `fpipe` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.17", features = ["fpipe"] }
```
