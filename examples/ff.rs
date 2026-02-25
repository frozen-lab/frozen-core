//! Example to test dummy usage of [`frozen_core::ffile::FrozenFile`]
//!
//! ## Usage
//!
//! - Run `cargo run --example ff w` to for the write mode
//! - Run `cargo run --example ff r` to for the read mode
//!
//! Read w/o write will always fail!!

use frozen_core::{
    error::FrozenRes,
    ffile::{FFCfg, FrozenFile},
};

const MID: u8 = 1;
const INIT_LEN: usize = 0x10 * 0x0A;

const DATA: &[u8] = b"frozen_storage_t";

fn main() -> FrozenRes<()> {
    let mut args = std::env::args().skip(1);

    let mode = args.next().expect("usage: ff <w|r>");
    let path = std::path::Path::new("./target/ff_example.data");

    let cfg = FFCfg {
        path: path.to_path_buf(),
        mid: MID,
        chunk_size: 0x10,
        initial_chunk_amount: 0x0A,
    };

    match mode.as_str() {
        "w" => write_mode(cfg),
        "r" => read_mode(cfg),
        _ => panic!("invalid mode, use `w` or `r`"),
    }
}

fn write_mode(cfg: FFCfg) -> FrozenRes<()> {
    let file = FrozenFile::new(cfg)?;
    assert_eq!(file.length().unwrap(), INIT_LEN);

    let iov = libc::iovec {
        iov_len: DATA.len(),
        iov_base: DATA.as_ptr() as *mut _,
    };

    file.write(&iov, 0)?;
    file.sync()
}

fn read_mode(cfg: FFCfg) -> FrozenRes<()> {
    let file = FrozenFile::new(cfg)?;
    assert_eq!(file.length().unwrap(), INIT_LEN);

    let mut buf = vec![0u8; DATA.len()];
    let mut iov = libc::iovec {
        iov_base: buf.as_mut_ptr() as *mut _,
        iov_len: buf.len(),
    };

    file.read(&mut iov, 0)?;
    assert_eq!(&buf, DATA);

    file.delete()
}
