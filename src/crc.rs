//! Implementation of CRC32C (Castagnoli polynomial) to compute a 32-bit cyclic redundancy check (CRC) using
//! Castagnoli polynomial, intended for data integrity verification for torn writes and curruption detection
//!
//! > [!WARNING]
//! > We assume little-endian target architecture, while big-endian architectures are not supported
//!
//! > [!IMPORTANT]
//! > The generated 32-bit CRC is not cryptographically secure, it's intended use is for data integrity in IO ops
//!
//! ## What is CRC?
//!
//! Cyclic Redundancy Check (CRC) is an err detecting code, e.g. 32 bits, used for data integrity in networking
//! protocols and storage systems, to check whether data has been altered, partially written/send or corrupted
//!
//! For a given buffer of data, e.g. `[u8; 0x100]`, we first compute a 32-bit crc, send/store it w/ the data, and
//! when received/read, again compute crc on the buffer and match it w/ the original, to check for integrity
//!
//! ## CRC32C
//!
//! CRC32C is a specific version of crc algo, which generates 32-bit crc using the Castagnoli polynomial
//!
//! It uses polynomial arithmetic in a finite field GF(2), i.e. Galois Field of order 2, i.e. {0, 1}, w/ `0x1EDC6F41`
//! as polynomial constant (init value), we use the refelected form `0x82F63B78` (little endian)

#[derive(Debug, PartialEq, Clone)]
enum Backend {
    Hardware,
    Software,
}

/// Implementation of CRC32C (Castagnoli polynomial) to compute a 32-bit cyclic redundancy check (CRC) using
/// Castagnoli polynomial
#[derive(Debug, Clone)]
pub struct Crc32C(Backend);

unsafe impl Send for Crc32C {}
unsafe impl Sync for Crc32C {}

impl Crc32C {
    /// Create a new instance of [`Crc32C`]
    ///
    /// ## CRC backend (Hardware vs Software)
    ///
    /// When the new instance is created, we select the fastest available backend,
    ///
    /// - On x86_64 we use `sse4.2` SIMD instructions when available
    /// - On aarch64 we use ARMv8 CRC instructions when available
    /// - Otherwise, fallback to portable software implementation
    ///
    /// Hardware acceleration is significantly faster than the software fallback, while both backend producing
    /// exact same CRC values
    ///
    /// ## Example
    ///
    /// ```
    /// let crc = frozen_core::crc::Crc32C::new();
    ///
    /// #[cfg(target_arch = "x86_64")]
    /// let expected = std::is_x86_feature_detected!("sse4.2");
    ///
    /// #[cfg(target_arch = "aarch64")]
    /// let expected = std::arch::is_aarch64_feature_detected!("crc");
    ///
    /// assert_eq!(crc.is_hardware_acceleration_available(), expected);
    /// ```
    pub fn new() -> Self {
        #[cfg(target_arch = "x86_64")]
        if std::is_x86_feature_detected!("sse4.2") {
            return Self(Backend::Hardware);
        }

        #[cfg(target_arch = "aarch64")]
        if std::arch::is_aarch64_feature_detected!("crc") {
            return Self(Backend::Hardware);
        }

        Self(Backend::Software)
    }

    /// Checks whether hardware acceleration is available at runtime
    pub fn is_hardware_acceleration_available(&self) -> bool {
        self.0 == Backend::Hardware
    }
}

/// Polynomial in refelected form (little endian) over `0x1EDC6F41`, used by CRC32C algorithm as init value
const CASTAGNOLI_POLYNOMIAL: u32 = 0x82F63B78;

/// Precomputed table of CRC32C values, for runtime perf by reducing computations at runtime,
///
/// ## Memory Footprint
///
/// Memory used is `0x100 * 4 * 8` i.e. `8 KiB`, which is stored in `.rodata` section
const CRC_TABLE: [[u32; 0x100]; 8] = {
    let mut table = [[0u32; 0x100]; 8];

    // table[0]
    let mut i = 0;
    while i < 0x100 {
        let mut crc = i as u32;
        let mut j = 0;

        while j < 8 {
            if (crc & 1) != 0 {
                crc = (crc >> 1) ^ CASTAGNOLI_POLYNOMIAL;
            } else {
                crc = crc >> 1;
            }

            j += 1;
        }

        table[0][i] = crc;
        i += 1;
    }

    // derive table[1..7] from table[0]
    let mut t = 1;
    while t < 8 {
        let mut n = 0;
        while n < 0x100 {
            let crc = table[t - 1][n];
            table[t][n] = (crc >> 8) ^ table[0][(crc & 0xFF) as usize];
            n += 1;
        }

        t += 1;
    }

    table
};

/// Software impl of CRC32C algo using [`CASTAGNOLI_POLYNOMIAL`] as init value
///
/// The length of `bytes_buf` must be >= 8
#[inline(always)]
fn crc32c_slice8(bytes_buf: &[u8]) -> u32 {
    // sanity check
    debug_assert!(bytes_buf.len() & 7 == 0);

    let mut crc = !0u32;
    let mut len = bytes_buf.len();
    let mut ptr = bytes_buf.as_ptr();

    // NOTE: we process 8 bytes at a time for ilp

    while len > 0 {
        let word = unsafe { core::ptr::read_unaligned(ptr as *const u64) };
        crc ^= word as u32;

        crc = CRC_TABLE[0][(crc & 0xFF) as usize]
            ^ CRC_TABLE[1][((crc >> 8) & 0xFF) as usize]
            ^ CRC_TABLE[2][((crc >> 0x10) & 0xFF) as usize]
            ^ CRC_TABLE[3][(crc >> 0x18) as usize]
            ^ CRC_TABLE[4][((word >> 0x20) & 0xFF) as usize]
            ^ CRC_TABLE[5][((word >> 0x28) & 0xFF) as usize]
            ^ CRC_TABLE[6][((word >> 0x30) & 0xFF) as usize]
            ^ CRC_TABLE[7][(word >> 0x38) as usize];

        ptr = unsafe { ptr.add(8) };
        len -= 8;
    }

    !crc
}
