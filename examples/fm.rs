use frozen_core::fmmap::{FMCfg, FrozenMMap};

const MID: u8 = 0;

#[repr(C)]
#[derive(Debug)]
struct Meta(u64);

unsafe impl Send for Meta {}
unsafe impl Sync for Meta {}

fn main() {
    let dir = std::path::PathBuf::from("./target/examples");
    let path = dir.join("fm_example.bin");

    let _ = std::fs::remove_file(&path);
    std::fs::create_dir_all(&dir).unwrap();

    let cfg = FMCfg {
        mid: MID,
        initial_count: 1,
        path: path.clone(),
        flush_duration: std::time::Duration::from_micros(100),
    };

    let mmap = FrozenMMap::<Meta>::new(cfg.clone()).unwrap();
    assert_eq!(mmap.slots(), 1);

    let (_, epoch) = mmap.write(0, |m| m.0 = 0x0A).unwrap();
    mmap.wait_for_durability(epoch).unwrap();

    let val = mmap.read(0, |m| m.0).unwrap();
    assert_eq!(val, 10);

    mmap.grow(1).unwrap();
    assert_eq!(mmap.slots(), 2);

    mmap.write(1, |m| m.0 = 0x0F).unwrap();
    drop(mmap); // syncs data

    // reopen & verify
    let reopened = FrozenMMap::<Meta>::new(cfg).unwrap();

    let v0 = reopened.read(0, |m| m.0).unwrap();
    let v1 = reopened.read(1, |m| m.0).unwrap();

    assert_eq!(v0, 0x0A);
    assert_eq!(v1, 0x0F);
}
