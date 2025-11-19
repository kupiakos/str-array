use super::*;

/// Failed to build `StrArray<N>` from a different-length `&str`.
#[derive(Clone, Copy)]
pub struct StrLenError<const N: usize> {
    pub src_len: usize,
}

impl<const N: usize> StrLenError<N> {
    /// Panic in `const` with this error.
    pub const fn const_panic(self) -> ! {
        panic!("Failed to build StrArray<N> from string with len != N")
    }
}

impl<const N: usize> Debug for StrLenError<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "StrLenError<{N}> {{ src_len: {} }}", self.src_len)
    }
}
impl<const N: usize> Display for StrLenError<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Failed to build `StrArray<{N}>` from string with len {}",
            self.src_len
        )
    }
}

#[cfg(any(has_core_error, feature = "std"))]
impl<const N: usize> Error for StrLenError<N> {}

/// Failed to build `CStrArray<N>` from a different-length `&CStr`.
#[derive(Clone, Copy)]
pub struct CStrLenError<const N: usize> {
    pub src_len: usize,
}

impl<const N: usize> CStrLenError<N> {
    /// Panic in `const` with this error.
    pub const fn const_panic(self) -> ! {
        panic!("Failed to build CStrArray<N> from string with len != N")
    }
}

impl<const N: usize> Debug for CStrLenError<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CStrLenError<{N}> {{ src_len: {} }}", self.src_len)
    }
}
impl<const N: usize> Display for CStrLenError<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Failed to build `CStrArray<{N}>` from string with len {}",
            self.src_len
        )
    }
}

#[cfg(any(has_core_error, feature = "std"))]
impl<const N: usize> Error for CStrLenError<N> {}

/// Data provided contains an interior nul byte at byte `position`.
#[derive(Clone, Copy, Debug)]
pub struct InteriorNulError {
    /// The position of the interior nul byte.
    pub position: usize,
}

impl InteriorNulError {
    /// Panic in `const` with this error.
    pub const fn const_panic(self) -> ! {
        panic!("Failed to build CStrArray with interior nul")
    }
}

impl Display for InteriorNulError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Interior nul at byte {}", self.position)
    }
}

#[cfg(any(has_core_error, feature = "std"))]
impl Error for InteriorNulError {}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;

    #[test]
    fn test_str_len_error_debug() {
        let err = StrLenError::<10> { src_len: 5 };
        assert_eq!(format!("{err:?}"), "StrLenError<10> { src_len: 5 }");
    }

    #[test]
    fn test_str_len_error_display() {
        let err = StrLenError::<10> { src_len: 5 };
        assert_eq!(
            format!("{err}"),
            "Failed to build `StrArray<10>` from string with len 5"
        );
    }

    #[test]
    fn test_c_str_len_debug() {
        let err = CStrLenError::<10> { src_len: 5 };
        assert_eq!(format!("{err:?}"), "CStrLenError<10> { src_len: 5 }");
    }

    #[test]
    fn test_c_str_len_display() {
        let err = CStrLenError::<10> { src_len: 5 };
        assert_eq!(
            format!("{err}"),
            "Failed to build `CStrArray<10>` from string with len 5"
        );
    }

    #[test]
    fn test_interior_nul_error_display() {
        let err = InteriorNulError { position: 10 };
        assert_eq!(format!("{err}"), "Interior nul at byte 10");
    }

    #[test]
    #[should_panic = "Failed to build StrArray<N> from string with len != N"]
    fn test_str_len_const_panic() {
        StrLenError::<10> { src_len: 5 }.const_panic()
    }

    #[test]
    #[should_panic = "Failed to build CStrArray<N> from string with len != N"]
    fn test_cstr_len_const_panic() {
        CStrLenError::<10> { src_len: 5 }.const_panic()
    }

    #[test]
    #[should_panic = "Failed to build CStrArray with interior nul"]
    fn test_interior_nul_const_panic() {
        InteriorNulError { position: 10 }.const_panic()
    }
}
