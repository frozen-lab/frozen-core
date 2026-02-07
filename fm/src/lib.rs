#![deny(missing_docs)]
#![allow(unsafe_op_in_unsafe_fn)]

//! Custom implementation of MemMap

mod error;

#[cfg(target_os = "linux")]
mod linux;

pub use error::FMErr;
