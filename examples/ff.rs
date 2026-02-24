//! Example to test dummy usage of [`frozen_core::ffile::FrozenFile`]
//!
//! ## Usage
//!
//! - Run `cargo run --example ff w` to for the write mode
//! - Run `cargo run --example ff r` to for the read mode
//!
//! Read w/o write will always fail!!

use frozen_core::{error::FrozenRes, ffile::FrozenFile};

const MID: u8 = 1;
const INIT_LEN: usize = 0x1000;

const DATA: &[u8] = b"grave_storage_engine";

fn main() -> FrozenRes<()> {
    let mut args = std::env::args().skip(1);

    let mode = args.next().expect("usage: ff <w|r>");
    let path = std::path::Path::new("./target/ff_example.data");

    match mode.as_str() {
        "w" => write_mode(path),
        "r" => read_mode(path),
        _ => panic!("invalid mode, use `w` or `r`"),
    }
}

fn write_mode(path: &std::path::Path) -> FrozenRes<()> {
    let file = FrozenFile::new(path, INIT_LEN, MID)?;
    assert_eq!(file.length(), INIT_LEN);

    let iov = libc::iovec {
        iov_base: DATA.as_ptr() as *mut _,
        iov_len: DATA.len(),
    };

    file.write(&iov, 0)?;
    file.sync()?;

    let mut bufs = [vec![1u8; 0x80], vec![2u8; 0x80]];
    let mut iovs: Vec<libc::iovec> = bufs
        .iter_mut()
        .map(|b| libc::iovec {
            iov_base: b.as_mut_ptr() as *mut _,
            iov_len: b.len(),
        })
        .collect();

    file.pwritev(&mut iovs, 0x400)?;
    file.sync()
}

fn read_mode(path: &std::path::Path) -> FrozenRes<()> {
    let file = FrozenFile::new(path, INIT_LEN, MID)?;

    let mut buf = vec![0u8; DATA.len()];
    let mut iov = libc::iovec {
        iov_base: buf.as_mut_ptr() as *mut _,
        iov_len: buf.len(),
    };

    file.read(&mut iov, 0)?;
    assert_eq!(&buf, DATA);

    let mut r1 = vec![0u8; 0x80];
    let mut r2 = vec![0u8; 0x80];

    let mut read_iovs = [
        libc::iovec {
            iov_base: r1.as_mut_ptr() as *mut _,
            iov_len: r1.len(),
        },
        libc::iovec {
            iov_base: r2.as_mut_ptr() as *mut _,
            iov_len: r2.len(),
        },
    ];

    file.preadv(&mut read_iovs, 0x400)?;
    assert!(r1.iter().all(|b| *b == 1));
    assert!(r2.iter().all(|b| *b == 2));

    file.delete()
}
