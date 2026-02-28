//! Custom implementations for [`Result<T>`] and [`Err<T>`]

/// Custom result type w/ [`FrozenErr`] as error type
pub type FrozenRes<T> = Result<T, FrozenErr>;

/// Custom error object used in [`FrozenRes`]
#[derive(Clone, Eq, PartialEq)]
pub struct FrozenErr {
    module: u8,
    domain: u8,
    reason: u16,
    detail: &'static [u8],
    errmsg: Vec<u8>,
}

impl FrozenErr {
    /// Constrcut a new instance from raw id's
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::error::FrozenErr;
    ///
    /// let err = FrozenErr::new(1, 2, 0x0033, b"io", b"failed".to_vec());
    /// assert_eq!(err.cmp(0x0033), true);
    /// ```
    #[inline]
    pub fn new(module: u8, domain: u8, reason: u16, detail: &'static [u8], errmsg: Vec<u8>) -> Self {
        Self {
            module,
            domain,
            reason,
            detail,
            errmsg,
        }
    }

    /// Compare [`Self::reason`] w/ given `reason` id
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::error::FrozenErr;
    ///
    /// let err = FrozenErr::new(1, 2, 42, b"test", Vec::new());
    /// assert!(err.cmp(42));
    /// assert!(!err.cmp(7));
    /// ```
    #[inline]
    pub fn cmp(&self, reason: u16) -> bool {
        self.reason == reason
    }

    /// Construct an `error_id` for [`FrozenErr`]
    ///
    /// ## Structure
    ///
    /// `| module:8 | domain:8 | reason:16 |`
    ///
    /// ## Example
    ///
    /// ```
    /// use frozen_core::error::FrozenErr;
    ///
    /// let err = FrozenErr::new(0x01, 0x02, 0x0033, b"io", Vec::new());
    /// let eid = err.error_id();
    ///
    /// assert_eq!(eid, 0x0102_0033);
    /// ```
    #[inline]
    pub const fn error_id(&self) -> u32 {
        ((self.module as u32) << 24) | ((self.domain as u32) << 16) | (self.reason as u32)
    }
}

impl core::fmt::Display for FrozenErr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let detail = core::str::from_utf8(&self.errmsg).unwrap_or("<non-utf8>");
        let errmsg = core::str::from_utf8(&self.errmsg).unwrap_or("<non-utf8>");

        #[cfg(test)]
        return write!(
            f,
            "[m={}, d={}, c={}] ({detail}) {errmsg}",
            self.module, self.domain, self.reason
        );

        #[cfg(not(test))]
        write!(f, "[{}] ({detail}) {errmsg}", self.error_id())
    }
}

impl core::fmt::Debug for FrozenErr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "\n----------\n")?;
        core::fmt::Display::fmt(self, f)?;
        write!(f, "\n----------\n")
    }
}

/// Default `module_id` for testing
///
/// It's only available inside test module across tests, and is never made available outside,
/// even when `cfg(test)` holds true, rust makes this possible for us ;)
#[cfg(test)]
pub const TEST_MID: u8 = 0x00;

#[cfg(test)]
mod tests {
    use super::*;

    #[inline]
    const fn from_error_id(eid: u32) -> (u8, u8, u16) {
        let module = ((eid >> 24) & 0xff) as u8;
        let domain = ((eid >> 16) & 0xff) as u8;
        let reason = (eid & 0xffff) as u16;
        (module, domain, reason)
    }

    #[test]
    fn ok_error_id_roundtrip_basic() {
        let err = FrozenErr::new(0x01, 0x02, 0x0033, b"io", Vec::new());
        let eid = err.error_id();

        assert_eq!(eid, 0x0102_0033);

        let (m, d, r) = from_error_id(eid);
        assert_eq!(m, 0x01);
        assert_eq!(d, 0x02);
        assert_eq!(r, 0x0033);
    }

    #[test]
    fn ok_error_id_roundtrip_edges() {
        let err = FrozenErr::new(0xff, 0x00, 0xffff, b"edge", Vec::new());
        let eid = err.error_id();

        assert_eq!(eid, 0xff00_ffff);

        let (m, d, r) = from_error_id(eid);
        assert_eq!(m, 0xff);
        assert_eq!(d, 0x00);
        assert_eq!(r, 0xffff);
    }

    #[test]
    fn ok_error_id_reason_only_changes_low_bits() {
        let e1 = FrozenErr::new(1, 2, 1, b"", Vec::new()).error_id();
        let e2 = FrozenErr::new(1, 2, 2, b"", Vec::new()).error_id();

        assert_eq!(e1 & 0xffff_0000, e2 & 0xffff_0000);
        assert_ne!(e1 & 0x0000_ffff, e2 & 0x0000_ffff);
    }
}
