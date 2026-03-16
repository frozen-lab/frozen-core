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

## FrozenErr

`FRes` & `FErr` are custom implementation's for result and error propagation.

To use the `error` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.14", features = ["error"] }
```

## Hints

The `hints` module provides stable friendly implementations of `likely` and `unlikely` branch hints functions.

To use the `hints` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.14", features = ["hints"] }
```

## FrozenFile

`FrozenFile` is a custom implementation of `std::fs::File`.

To use the `ffile` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.14", features = ["ffile"] }
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

## FrozenMMap

`FrozenMMap` is a custom implementation of `mmap`.

To use the `fmmap` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.14", features = ["fmmap"] }
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
frozen-core = { version = "0.0.14", features = ["crc32"] }
```

`Crc32C` is available on following architectures,

| Architecture    | Support |
|-----------------|:-------:|
| `aarch64`       | ✅      |
| `x86_64`        | ✅      |

## BPool

Lock-free buffer pool used for staging IO buffers.

To use the `bpool` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.14", features = ["bpool"] }
```

## MPSCQ

A lock-free multi-producer single-consumer queue.

To use the `mpscq` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.14", features = ["mpscq"] }
```

## FrozenPipe

An high throughput asynchronous IO pipeline for chunk based storage, it uses batches to write requests and flushes
them in the background, while providing durability guarantees via epochs.

To use the `fpipe` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.14", features = ["fpipe"] }
```
