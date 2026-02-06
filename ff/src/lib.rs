#![deny(missing_docs)]
#![deny(unused_must_use)]
#![allow(unsafe_op_in_unsafe_fn)]

//! Custom implementation of File

mod error;

#[cfg(target_os = "linux")]
#[allow(unused)]
mod linux;

pub use error::FFErr;
