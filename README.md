# FrozenCore

Custom implementations and core utilities for frozen codebases.

## Index

- [`usage`](#usage)
- [`ffile`](#frozenfile)
- [`fmmap`](#frozenmmap)
- [`error`](#frozenerr)
- [`hints`](#hints)
- [`notes`](#notes)

## Usage

Add following to your `Cargo.toml`,

```toml
[dependencies]
frozen-core = { version = "0.0.6", default-features = true }
```

> [!TIP]
> All the features available by default. To disable this, set `default-features = false`

## FrozenFile

`FrozenFile` is a custom implementation of `std::fs::File`.

To use the `ffile` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.6", default-features = false, features = ["ffile"] }
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
frozen-core = { version = "0.0.6", default-features = false, features = ["fmmap"] }
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
use frozen_core::ffile::{FrozenFile, FFCfg};

let dir = tempfile::tempdir().unwrap();
let path = dir.path().join("tmp_frozen_file");

let cfg = FFCfg {
    mid: 0x00,
    chunk_size: 0x10,
    path: path.to_path_buf(),
    initial_chunk_amount: 0x0A,
};

let file = FrozenFile::new(cfg).unwrap();
assert_eq!(file.length().unwrap(), 0x10 * 0x0A);
```

## FrozenErr

`FRes` & `FErr` are custom implementation's for result and error propogation.

To use the `error` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.6", default-features = false, features = ["error"] }
```

## Hints

The `hints` module provides stable friendly implementations of `likely` and `unlikely` branch hints functions.

To use the `hints` module, add it as a dependency in your `Cargo.toml`:

```toml
[dependencies]
frozen-core = { version = "0.0.6", default-features = false, features = ["hints"] }
```

## Notes

> [!IMPORTANT]
> `frozen-core` is primarily created for [frozen-lab](https://github.com/frozen-lab/) projects.
> External use is discouraged, but not prohibited, given __you asume all the risks__.

This project is licensed under the Apache-2.0 and MIT License. 
See the [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT) file for more details.

Contributions are welcome! Please feel free to submit a PR or open an issue if you have any feedback or suggestions.
