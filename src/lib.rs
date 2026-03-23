#![deny(missing_docs)]
#![allow(unsafe_op_in_unsafe_fn)]
#![doc = include_str!("../README.md")]

#[cfg(any(test, feature = "error"))]
pub mod error;

#[cfg(any(test, feature = "hints"))]
pub mod hints;

#[cfg(any(test, feature = "crc32"))]
pub mod crc32;

#[cfg(any(test, feature = "bpool"))]
pub mod bpool;

#[cfg(any(test, feature = "mpscq"))]
pub mod mpscq;

#[cfg(any(test, feature = "ffile"))]
pub mod ffile;

#[cfg(any(test, feature = "fmmap"))]
pub mod fmmap;

#[cfg(any(test, feature = "fpipe"))]
pub mod fpipe;

#[cfg(any(test, feature = "fbits"))]
pub mod fbits;
