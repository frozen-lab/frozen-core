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
//! It uses polynomial arithmetic in GF(2), the generator polynomial for CRC32C is `0x1EDC6F41`, and we use the
//! reflected form `0x82F63B78`, which is required by little-endian streaming algorithms
//!
//! ## Example
//!
//! ```
//! let crc = frozen_core::crc::Crc32C::new();
//!
//! #[cfg(target_arch = "x86_64")]
//! let expected = std::is_x86_feature_detected!("sse4.2");
//!
//! #[cfg(target_arch = "aarch64")]
//! let expected = std::arch::is_aarch64_feature_detected!("crc");
//!
//! assert_eq!(crc.is_hardware_acceleration_available(), expected);
//! ```

#[derive(Debug, PartialEq, Clone, Copy)]
enum Backend {
    Hardware,
    Software,
}

type TCrc = u32;
type TBuf = [u8];

/// Implementation of CRC32C (Castagnoli polynomial) to compute a 32-bit cyclic redundancy check (CRC) using
/// Castagnoli polynomial
#[derive(Debug, PartialEq, Clone, Copy)]
pub struct Crc32C(Backend);

impl Crc32C {
    /// Create a new instance of [`Crc32C`]
    ///
    /// ## CRC backend (Hardware vs Software)
    ///
    /// When the new instance is created, we select the fastest available backend,
    ///
    /// - On x86_64 we use `sse4.2` SIMD instructions when available
    /// - On aarch64 we use ARMv8 `crc` instructions when available
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

    /// Compute CRC32C for given `buf` to generate 32-bit crc
    ///
    /// **NOTE:** Length of `buf` must be a multiple of 8
    ///
    /// At runtime we choose the fastest available backend,
    ///
    /// - x86_64: `sse4.2` when available
    /// - aarch64: ArmV8 `crc` instruction when available
    /// - fallback: software castagnoli impl
    ///
    /// All backends produce identical CRC32C values
    pub fn crc(&self, buf: &TBuf) -> TCrc {
        match self.0 {
            Backend::Software => crc32c_slice8(buf),
            Backend::Hardware => {
                #[cfg(target_arch = "x86_64")]
                return unsafe { crc32c_hardware(buf) };

                #[cfg(target_arch = "aarch64")]
                unimplemented!()
            }
        }
    }

    /// Compute CRC32C for two bufs in parallel using `Instruction Level Parallelism` to generate 32-bit crc
    /// for each buf (mapped one-to-one)
    ///
    /// **NOTE:** Length of each `buf` must be equal and a multiple of 8
    ///
    /// At runtime we choose the fastest available backend,
    ///
    /// - x86_64: `sse4.2` when available
    /// - aarch64: ArmV8 `crc` instruction when available
    /// - fallback: software castagnoli impl
    ///
    /// All backends produce identical CRC32C values
    pub fn crc_2x(&self, buffers: [&TBuf; 2]) -> [TCrc; 2] {
        match self.0 {
            Backend::Software => crc32c_slice8_2x(buffers),
            Backend::Hardware => {
                #[cfg(target_arch = "x86_64")]
                return unsafe { crc32c_hardware_2x(buffers) };

                #[cfg(target_arch = "aarch64")]
                unimplemented!()
            }
        }
    }

    /// Compute CRC32C for four bufs in parallel using `Instruction Level Parallelism` to generate 32-bit crc
    /// for each buf (mapped one-to-one)
    ///
    /// **NOTE:** Length of each `buf` must be equal and a multiple of 8
    ///
    /// At runtime we choose the fastest available backend,
    ///
    /// - x86_64: `sse4.2` when available
    /// - aarch64: ArmV8 `crc` instruction when available
    /// - fallback: software castagnoli impl
    ///
    /// All backends produce identical CRC32C values
    pub fn crc_4x(&self, buffers: [&TBuf; 4]) -> [TCrc; 4] {
        match self.0 {
            Backend::Software => crc32c_slice8_4x(buffers),
            Backend::Hardware => {
                #[cfg(target_arch = "x86_64")]
                return unsafe { crc32c_hardware_4x(buffers) };

                #[cfg(target_arch = "aarch64")]
                unimplemented!()
            }
        }
    }
}

/// Polynomial in refelected form (little endian) over `0x1EDC6F41`, used by CRC32C algorithm as init value
const CASTAGNOLI_POLYNOMIAL: TCrc = 0x82F63B78;

/// Precomputed table of CRC32C values, for runtime perf by reducing computations at runtime,
///
/// ## Memory Footprint
///
/// Memory used is `0x100 * 4 * 8` i.e. `8 KiB`, which is stored in `.rodata` section
const CRC_TABLE: [[TCrc; 0x100]; 8] = {
    let mut table = [[0; 0x100]; 8];

    // table[0]
    let mut i = 0;
    while i < 0x100 {
        let mut crc = i as TCrc;
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

/// Compute CRC32C for `buf` w/ Software Castagnoli impl, to generate 32-bit crc
///
/// **NOTE:** Length of buffer must be a multiple of 8
#[inline(always)]
fn crc32c_slice8(buf: &TBuf) -> TCrc {
    // sanity check
    debug_assert!(buf.len() & 7 == 0);

    let table = &CRC_TABLE;

    let mut crc: TCrc = !0;
    let mut len = buf.len();
    let mut ptr = buf.as_ptr();

    while len > 0 {
        let word: u64 = unsafe { core::ptr::read_unaligned(ptr as *const u64) };
        crc ^= word as TCrc;

        crc = table[0][(crc & 0xFF) as usize]
            ^ table[1][((crc >> 8) & 0xFF) as usize]
            ^ table[2][((crc >> 0x10) & 0xFF) as usize]
            ^ table[3][(crc >> 0x18) as usize]
            ^ table[4][((word >> 0x20) & 0xFF) as usize]
            ^ table[5][((word >> 0x28) & 0xFF) as usize]
            ^ table[6][((word >> 0x30) & 0xFF) as usize]
            ^ table[7][(word >> 0x38) as usize];

        ptr = unsafe { ptr.add(8) };
        len -= 8;
    }

    !crc
}

/// Compute CRC32C for two bufs in parallel using `Instruction Level Parallelism` w/ Software Castagnoli impl,
/// to generate 32-bit crc for each buf (mapped one-to-one)
///
/// **NOTE:** Length of each buf must be equal and a multiple of 8
#[inline(always)]
fn crc32c_slice8_2x(buffers: [&TBuf; 2]) -> [TCrc; 2] {
    let mut len = buffers[0].len();

    // sanity checks
    debug_assert!(len & 7 == 0, "bytes_buf must be 8 bytes aligned");
    debug_assert!(
        buffers.iter().all(|b| b.len() == len),
        "each buf in bytes_bufs must be of same length"
    );

    let table = &CRC_TABLE;

    let mut crc0: u32 = !0;
    let mut crc1: u32 = !0;

    let mut p0 = buffers[0].as_ptr();
    let mut p1 = buffers[1].as_ptr();

    while len > 0 {
        unsafe {
            let w0: u64 = core::ptr::read_unaligned(p0 as *const u64);
            let w1: u64 = core::ptr::read_unaligned(p1 as *const u64);

            crc0 ^= w0 as TCrc;
            crc1 ^= w1 as TCrc;

            crc0 = table[0][(crc0 & 0xFF) as usize]
                ^ table[1][((crc0 >> 8) & 0xFF) as usize]
                ^ table[2][((crc0 >> 0x10) & 0xFF) as usize]
                ^ table[3][(crc0 >> 0x18) as usize]
                ^ table[4][((w0 >> 0x20) & 0xFF) as usize]
                ^ table[5][((w0 >> 0x28) & 0xFF) as usize]
                ^ table[6][((w0 >> 0x30) & 0xFF) as usize]
                ^ table[7][(w0 >> 0x38) as usize];

            crc1 = table[0][(crc1 & 0xFF) as usize]
                ^ table[1][((crc1 >> 8) & 0xFF) as usize]
                ^ table[2][((crc1 >> 0x10) & 0xFF) as usize]
                ^ table[3][(crc1 >> 0x18) as usize]
                ^ table[4][((w1 >> 0x20) & 0xFF) as usize]
                ^ table[5][((w1 >> 0x28) & 0xFF) as usize]
                ^ table[6][((w1 >> 0x30) & 0xFF) as usize]
                ^ table[7][(w1 >> 0x38) as usize];

            p0 = p0.add(8);
            p1 = p1.add(8);
        }

        len -= 8;
    }

    [!crc0, !crc1]
}

/// Compute CRC32C for four bufs in parallel using `Instruction Level Parallelism` w/ Software Castagnoli impl,
/// to generate 32-bit crc for each buf (mapped one-to-one)
///
/// **NOTE:** Length of each buf must be equal and a multiple of 8
#[inline(always)]
fn crc32c_slice8_4x(buffers: [&TBuf; 4]) -> [TCrc; 4] {
    let mut len = buffers[0].len();

    // sanity checks
    debug_assert!(len & 7 == 0, "bytes_buf must be 8 bytes aligned");
    debug_assert!(
        buffers.iter().all(|b| b.len() == len),
        "each buf in bytes_bufs must be of same length"
    );

    let table = &CRC_TABLE;

    let mut crc0: TCrc = !0;
    let mut crc1: TCrc = !0;
    let mut crc2: TCrc = !0;
    let mut crc3: TCrc = !0;

    let mut p0 = buffers[0].as_ptr();
    let mut p1 = buffers[1].as_ptr();
    let mut p2 = buffers[2].as_ptr();
    let mut p3 = buffers[3].as_ptr();

    while len > 0 {
        unsafe {
            let w0: u64 = core::ptr::read_unaligned(p0 as *const u64);
            let w1: u64 = core::ptr::read_unaligned(p1 as *const u64);
            let w2: u64 = core::ptr::read_unaligned(p2 as *const u64);
            let w3: u64 = core::ptr::read_unaligned(p3 as *const u64);

            crc0 ^= w0 as TCrc;
            crc1 ^= w1 as TCrc;
            crc2 ^= w2 as TCrc;
            crc3 ^= w3 as TCrc;

            crc0 = table[0][(crc0 & 0xFF) as usize]
                ^ table[1][((crc0 >> 8) & 0xFF) as usize]
                ^ table[2][((crc0 >> 0x10) & 0xFF) as usize]
                ^ table[3][(crc0 >> 0x18) as usize]
                ^ table[4][((w0 >> 0x20) & 0xFF) as usize]
                ^ table[5][((w0 >> 0x28) & 0xFF) as usize]
                ^ table[6][((w0 >> 0x30) & 0xFF) as usize]
                ^ table[7][(w0 >> 0x38) as usize];

            crc1 = table[0][(crc1 & 0xFF) as usize]
                ^ table[1][((crc1 >> 8) & 0xFF) as usize]
                ^ table[2][((crc1 >> 0x10) & 0xFF) as usize]
                ^ table[3][(crc1 >> 0x18) as usize]
                ^ table[4][((w1 >> 0x20) & 0xFF) as usize]
                ^ table[5][((w1 >> 0x28) & 0xFF) as usize]
                ^ table[6][((w1 >> 0x30) & 0xFF) as usize]
                ^ table[7][(w1 >> 0x38) as usize];

            crc2 = table[0][(crc2 & 0xFF) as usize]
                ^ table[1][((crc2 >> 8) & 0xFF) as usize]
                ^ table[2][((crc2 >> 0x10) & 0xFF) as usize]
                ^ table[3][(crc2 >> 0x18) as usize]
                ^ table[4][((w2 >> 0x20) & 0xFF) as usize]
                ^ table[5][((w2 >> 0x28) & 0xFF) as usize]
                ^ table[6][((w2 >> 0x30) & 0xFF) as usize]
                ^ table[7][(w2 >> 0x38) as usize];

            crc3 = table[0][(crc3 & 0xFF) as usize]
                ^ table[1][((crc3 >> 8) & 0xFF) as usize]
                ^ table[2][((crc3 >> 0x10) & 0xFF) as usize]
                ^ table[3][(crc3 >> 0x18) as usize]
                ^ table[4][((w3 >> 0x20) & 0xFF) as usize]
                ^ table[5][((w3 >> 0x28) & 0xFF) as usize]
                ^ table[6][((w3 >> 0x30) & 0xFF) as usize]
                ^ table[7][(w3 >> 0x38) as usize];

            p0 = p0.add(8);
            p1 = p1.add(8);
            p2 = p2.add(8);
            p3 = p3.add(8);
        }

        len -= 8;
    }

    [!crc0, !crc1, !crc2, !crc3]
}

/// Compute CRC32C w/ `sse4.2` SIMD ISA, to generate 32-bit crc
///
/// **NOTE:** Length of `buf` must be a multiple of 8
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "sse4.2")]
unsafe fn crc32c_hardware(buf: &TBuf) -> TCrc {
    // sanity check
    debug_assert!(buf.len() & 7 == 0, "bytes_buf must be 8 bytes aligned");

    let mut crc: u64 = !0;
    let mut len = buf.len();
    let mut ptr = buf.as_ptr();

    while len > 0 {
        let word = core::ptr::read_unaligned(ptr as *const u64);
        crc = core::arch::x86_64::_mm_crc32_u64(crc, word);
        ptr = ptr.add(8);

        len -= 8;
    }

    (!crc) as TCrc
}

/// Compute CRC32C for two bufs in parallel using `Instruction Level Parallelism` w/ `sse4.2` SIMD ISA,
/// to generate 32-bit crc for each buf (mapped one-to-one)
///
/// **NOTE:** Length of each buf must be equal and a multiple of 8
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "sse4.2")]
unsafe fn crc32c_hardware_2x(buffers: [&TBuf; 2]) -> [TCrc; 2] {
    let mut len = buffers[0].len();

    // sanity checks
    debug_assert!(len & 7 == 0, "bytes_buf must be 8 bytes aligned");
    debug_assert!(
        buffers.iter().all(|b| b.len() == len),
        "each buf in bytes_bufs must be of same length"
    );

    let mut c0: u64 = !0;
    let mut c1: u64 = !0;

    let mut p0 = buffers[0].as_ptr();
    let mut p1 = buffers[1].as_ptr();

    while len > 0 {
        let w0 = core::ptr::read_unaligned(p0 as *const u64);
        let w1 = core::ptr::read_unaligned(p1 as *const u64);

        c0 = core::arch::x86_64::_mm_crc32_u64(c0, w0);
        c1 = core::arch::x86_64::_mm_crc32_u64(c1, w1);

        p0 = p0.add(8);
        p1 = p1.add(8);
        len -= 8;
    }

    [!(c0 as TCrc), !(c1 as TCrc)]
}

/// Compute CRC32C for four bufs in parallel using `Instruction Level Parallelism` w/ `sse4.2` SIMD ISA,
/// to generate 32-bit crc for each buf (mapped one-to-one)
///
/// **NOTE:** Length of each buffer must be equal and a multiple of 8
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "sse4.2")]
unsafe fn crc32c_hardware_4x(buffers: [&TBuf; 4]) -> [TCrc; 4] {
    let mut len = buffers[0].len();

    // sanity checks
    debug_assert!(len & 7 == 0, "bytes_buf must be 8 bytes aligned");
    debug_assert!(
        buffers.iter().all(|b| b.len() == len),
        "each buf in bytes_bufs must be of same length"
    );

    let mut c0: u64 = !0;
    let mut c1: u64 = !0;
    let mut c2: u64 = !0;
    let mut c3: u64 = !0;

    let mut p0 = buffers[0].as_ptr();
    let mut p1 = buffers[1].as_ptr();
    let mut p2 = buffers[2].as_ptr();
    let mut p3 = buffers[3].as_ptr();

    while len > 0 {
        let w0 = core::ptr::read_unaligned(p0 as *const u64);
        let w1 = core::ptr::read_unaligned(p1 as *const u64);
        let w2 = core::ptr::read_unaligned(p2 as *const u64);
        let w3 = core::ptr::read_unaligned(p3 as *const u64);

        c0 = core::arch::x86_64::_mm_crc32_u64(c0, w0);
        c1 = core::arch::x86_64::_mm_crc32_u64(c1, w1);
        c2 = core::arch::x86_64::_mm_crc32_u64(c2, w2);
        c3 = core::arch::x86_64::_mm_crc32_u64(c3, w3);

        p0 = p0.add(8);
        p1 = p1.add(8);
        p2 = p2.add(8);
        p3 = p3.add(8);

        len -= 8;
    }

    [!(c0 as TCrc), !(c1 as TCrc), !(c2 as TCrc), !(c3 as TCrc)]
}

#[cfg(test)]
mod tests {
    use super::*;

    mod software {
        use super::*;

        #[test]
        fn ilp_consistency_2x() {
            let buf = vec![0xABu8; 0x1000];

            let c1 = crc32c_slice8(&buf);
            let [c2a, c2b] = crc32c_slice8_2x([&buf, &buf]);

            assert_eq!(c1, c2a);
            assert_eq!(c1, c2b);
        }

        #[test]
        fn ilp_consistency_4x() {
            let buf = vec![0xABu8; 0x1000];

            let c1 = crc32c_slice8(&buf);
            let [c4a, c4b, c4c, c4d] = crc32c_slice8_4x([&buf, &buf, &buf, &buf]);

            assert_eq!(c1, c4a);
            assert_eq!(c1, c4b);
            assert_eq!(c1, c4c);
            assert_eq!(c1, c4d);
        }
    }
}
