#![no_std]
#![deny(missing_docs)]
#![allow(unsafe_op_in_unsafe_fn)]
#![doc = include_str!("../README.md")]

extern crate alloc;

#[cfg(any(test, feature = "error"))]
pub mod error;

#[cfg(any(test, feature = "hints"))]
pub mod hints;

#[cfg(any(test, feature = "ffile"))]
pub mod ffile;

#[cfg(any(test, feature = "fmmap"))]
pub mod fmmap;
