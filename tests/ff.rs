use frozen_core::ffile::{FFileErrRes, FrozenFile};
use std::{
    fs::{set_permissions, Permissions},
    os::unix::fs::PermissionsExt,
    path::Path,
};

const INIT_LEN: u64 = 0;
const TEST_MID: u8 = 0;

fn new_tmp(id: &'static [u8]) -> (Vec<u8>, FrozenFile) {
    let mut path = Vec::with_capacity(b"./target/".len() + id.len());
    path.extend_from_slice(b"./target/");
    path.extend_from_slice(id);

    let file = FrozenFile::new(path.clone(), INIT_LEN, TEST_MID).expect("new FrozenFile");

    (path, file)
}

#[test]
fn new_fails_when_no_write_perm() {
    // NOTE: When running as root (UID 0), perm (read & write) checks are bypassed
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    if unsafe { libc::geteuid() } == 0 {
        panic!("Tests must not run as root (UID 0); root bypasses Unix file permission checks");
    }

    let (path, file) = new_tmp(b"frozenfile_open");

    // read-only permission
    drop(file);

    let p = Path::new(std::str::from_utf8(&path).expect("utf8 path"));
    set_permissions(p, Permissions::from_mode(0o400)).expect("chmod");

    let err = FrozenFile::new(path, INIT_LEN, TEST_MID).expect_err("must fail");
    assert!(err.cmp(FFileErrRes::Red as u16))
}

#[test]
fn new_fails_when_no_perm() {
    // NOTE: When running as root (UID 0), perm (read & write) checks are bypassed
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    if unsafe { libc::geteuid() } == 0 {
        panic!("Tests must not run as root (UID 0); root bypasses Unix file permission checks");
    }

    let (path, file) = new_tmp(b"frozenfile_open");

    // read-only permission
    drop(file);
    let p = Path::new(std::str::from_utf8(&path).expect("utf8 path"));
    set_permissions(p, Permissions::from_mode(0o000)).expect("chmod");

    let err = FrozenFile::new(path, INIT_LEN, TEST_MID).expect_err("must fail");
    assert!(err.cmp(FFileErrRes::Red as u16))
}
