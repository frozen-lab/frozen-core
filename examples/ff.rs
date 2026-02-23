use frozen_core::{error::FrozenRes, ffile::FrozenFile};
use libc::iovec;
use std::path::Path;

const MID: u8 = 1;

fn main() -> FrozenRes<()> {
    let path = Path::new("./target/grave_example.data");

    let file = FrozenFile::new(path, 0x1000, MID)?;
    assert_eq!(file.length(), 0x1000);

    let data = b"grave_storage_engine";
    let iov = iovec {
        iov_base: data.as_ptr() as *mut _,
        iov_len: data.len(),
    };

    file.write(&iov, 0)?;
    file.sync()?;

    let mut check = vec![0u8; data.len()];
    let mut check_iov = iovec {
        iov_base: check.as_mut_ptr() as *mut _,
        iov_len: check.len(),
    };

    file.read(&mut check_iov, 0)?;
    assert_eq!(&check, data);

    let mut bufs = [vec![1u8; 0x80], vec![2u8; 0x80]];
    let mut iovs: Vec<iovec> = bufs
        .iter_mut()
        .map(|b| iovec {
            iov_base: b.as_mut_ptr() as *mut _,
            iov_len: b.len(),
        })
        .collect();

    file.pwritev(&mut iovs, 0x400)?;
    file.sync()?;

    let mut r1 = vec![0u8; 0x80];
    let mut r2 = vec![0u8; 0x80];

    let mut read_iovs = [
        iovec {
            iov_base: r1.as_mut_ptr() as *mut _,
            iov_len: r1.len(),
        },
        iovec {
            iov_base: r2.as_mut_ptr() as *mut _,
            iov_len: r2.len(),
        },
    ];

    file.preadv(&mut read_iovs, 0x400)?;
    assert!(r1.iter().all(|b| *b == 1));
    assert!(r2.iter().all(|b| *b == 2));

    // drop and reopen to verify durability
    drop(file);

    let reopened = FrozenFile::new(path, 0x1000, MID)?;
    let mut buf = vec![0u8; data.len()];
    let mut read_iov = iovec {
        iov_base: buf.as_mut_ptr() as *mut _,
        iov_len: buf.len(),
    };

    reopened.read(&mut read_iov, 0)?;
    assert_eq!(&buf, data);

    // cleanup
    reopened.delete()?;
    assert!(!path.exists());

    Ok(())
}
