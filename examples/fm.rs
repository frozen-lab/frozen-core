use frozen_core::{
    fe::FECheckOk,
    ff::{FFCfg, FrozenFile},
    fm::{FMCfg, FrozenMMap},
};

const MODULE_ID: u8 = 0;

fn main() {
    let dir = std::path::PathBuf::from("/tmp/frozen-core/examples");
    let path = dir.join("fm_example.bin");
    std::fs::create_dir_all(&dir).expect("create example dir");

    let ff = FrozenFile::new(FFCfg::new(path, MODULE_ID), 8).expect("file");
    let fm = FrozenMMap::new(ff.fd(), 8, FMCfg::new(MODULE_ID)).expect("mmap");

    {
        let w = fm.writer::<u64>(0).expect("writer");
        assert!(w.write(|v| *v = 0xDEADBEEF).check_ok());
    }

    assert!(fm.sync().check_ok());

    let r = fm.reader::<u64>(0).expect("reader");
    let value = r.read(|v| *v);

    assert_eq!(value, 0xDEADBEEF);
}
