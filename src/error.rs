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
    /// constrcut a new instance from raw id's
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

    /// compare [`Self::reason`] w/ given `reason` id
    #[inline]
    pub fn cmp(&self, reason: u16) -> bool {
        self.reason == reason
    }

    /// construct an `error_id` for [`FrozenErr`]
    ///
    /// ## Structure
    ///
    /// `| module:8 | domain:8 | reason:16 |`
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
        write!(f, "[0x{:08x}] ({detail}) {errmsg}", self.error_id())
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
#[cfg(test)]
pub const TEST_MID: u8 = 0x00;
