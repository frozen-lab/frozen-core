# Changelog

## `0.0.18`

- Added benches for `crc32` module
- Added benches for `bpool` module
- Added benches for `mpscq` module
- Impl of `FMTransaction` for transactional writes in `FrozenMMap`

## `0.0.17`

- `FrozenMMap`
  - Impl of `FrozenMMap::memory_usage()`
  - Improved internal locking (to fix random SIGSEGV errors)
  - Improved `FrozenMMap::read()` throughput (yanked io_locking)

## `0.0.16`

- `FrozenMMap`
  - Improved Docs
  - Yanked `FrozenMMap::grow`
  - Impl of `FrozenMMap::new_grown`
  - Yanked internal locking for `FrozenMMap`

## `0.0.15`

- Improved notes (internal docs)
- Improved `FrozenMMap::new` api
- Improved `FrozenPipe::new` api
- Improved `MODULE_ID` handling

## `0.0.14`

- Optimized vectored IO for `FrozenFile` on `POSIX` systems

## `0.0.13`

- Improved error handling for `ffile`, `fmmap`, `bpool` & `fpipe` modules
  - **BREAKING:** All error types are private
- No features are available by default

## `0.0.12`

- Impl of `write_sync` in `FrozenMMap`
- Improved epoch handling for `FrozenPipe`

## `0.0.11`

- Impl of `f_advise_raw` (linux only best effort syscall) for `FrozenFile`
- Use of _io_lock_ in `FrozenPipe`

## `0.0.10`

- Impl of `mpscq` module
- Impl of dynamic allocations in `BPool` (via `BPool::allocate_dynamic`)
- Yanked use of lifetimes from `bpool::Allocation` object, w/ use of raw pointer internally
- Impl of `fpipe` module for batch io ops

## `0.0.9`

- Impl of `bpool` module 

## `0.0.8`

- Impl of `crc` module

## `0.0.7`

- `FF`
  - improved public api
  - revised test suites
  - impl of `sync_range` (linux only)
  - impl of vectored write/read ops
  - impl of exclusive locking to prevent simultaneously running multiple instances
  - updated example
  - impl of `FFCfg`
- `FM`
  - improved publinc api
  - impl of `grow` and `delete`
  - completely thread safe, parallel ops on same index w/ internal locking
  - impl of `wait_for_durability`
  - added durability guarantees for write ops
  - simplified locking mechanism

## `0.0.6`

- `FF` improved public api
- `FM` module
  - added `epoch` ids for every writes
  - added `wait_for_durability` to enable waiting for durability
- improved test coverage (80+ tests)
- improved docs

## `0.0.5`

- improved error propogation
- all modules are behind feature flags (all available by default)
- failed attempt to go `no_std`

## `0.0.4`

- `FF` module
  - Yanked `read` & `write` ops
  - Migrated io ops to use `iovecs` for linux impl
  - (Rename) `FF` -> `FrozenFile`
  - Added `mac` support
- `FM` module
  - (Rename) `FM` -> `FrozenMMap`
  - Added `mac` support

## `0.0.3`

- Improved `docs`
- Added `examples/`

## `0.0.2`

- Improved `FFCfg` & `FMCfg` w/ builder pattern construction

## `0.0.1`

- Impl of `fe` (Frozen Error) for custom error repr
- Impl of `hints` module for compiler/branching hints
- Impl of `ff` (FrozenFile) w/ `Linux` (x86 & aarch64)
- Impl of `fm` (FrozenMMAp) w/ `Linux` (x86 & aarch64)
