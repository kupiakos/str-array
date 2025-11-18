use core::slice;
use core::{ffi::CStr, num::NonZeroU8};

use super::*;
use crate::error::{CStrLenError, InteriorNulError};
use NulByte::Nul;

/// A byte that must always be 0.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[repr(u8)]
enum NulByte {
    Nul = 0,
}

const fn count_bytes(val: &CStr) -> usize {
    // Avoid bumping the MSRV and stay `const` by using `unsafe`.
    let mut p = val.as_ptr();
    let mut other_len = 0;
    while unsafe { *p } != 0 {
        other_len += 1;
        p = unsafe { p.add(1) };
    }
    other_len
}

/// Fixed-size [`CStr`] stored as an array.
///
/// The length `N` is the number of bytes in the string _not_ including the nul terminator.
///
/// Because it has a fixed size, it can be put directly in a `static` and all
/// casting operations are constant-time.
// Note: As of writing, `&mut CStr` is not sound to construct.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[repr(C)]
pub struct CStrArray<const N: usize> {
    data: [NonZeroU8; N],
    nul: NulByte,
}

impl<const N: usize> CStrArray<N> {
    /// Builds a `StrArray<N>` from `val`.
    ///
    /// This returns an `Err` if `val.len() != N`.
    ///
    /// If `val` is a literal or `const`, consider using [`cstr_array!`]
    /// instead, which always builds a `CStrArray` with the correct `N`
    /// by checking the length at compile time.
    pub const fn new(val: &CStr) -> Result<Self, CStrLenError<N>> {
        let other_len = count_bytes(val);
        if other_len != N {
            return Err(CStrLenError { src_len: other_len });
        }
        // SAFETY: `val` is checked to point to `N` non-nul bytes followed by a nul.
        Ok(unsafe { Self::new_unchecked(val) })
    }

    /// Builds a `StrArray<N>` from `val` without a size check.
    ///
    /// # Safety
    ///
    /// `val.count_bytes() == N`
    pub const unsafe fn new_unchecked(val: &CStr) -> Self {
        // SAFETY: `val` is known to point to `N` non-nul bytes followed by a nul.
        CStrArray {
            data: unsafe { *val.as_ptr().cast() },
            nul: Nul,
        }
    }

    /// Constructs a `CStrArray<N>` from an array with its byte contents.
    ///
    /// Note that `bytes` should _not_ include the nul terminator -
    /// it is appended automatically by this method.
    ///
    /// If `val` is a literal or `const`, consider using [`cstr_array!`]
    /// instead, which checks for the presence of a nul at compile time.
    pub const fn from_bytes_without_nul(bytes: &[u8; N]) -> Result<Self, InteriorNulError> {
        // Avoid bumping the MSRV and stay `const` by using a manual loop.
        let mut i = 0;
        while i < N {
            if bytes[i] == 0 {
                return Err(InteriorNulError { position: i });
            }
            i += 1;
        }
        // SAFETY: `bytes` has been checked to contain no interior nul bytes
        unsafe { Self::from_bytes_without_nul_unchecked(bytes) }
    }

    /// Constructs a `CStrArray<N>` from an array with its byte contents and no checks.
    ///
    /// Note that this does _not_ include the nul terminator -
    /// it is appended automatically.
    ///
    /// # Safety
    /// - `bytes` must not have any 0 (nul) bytes.
    pub const unsafe fn from_bytes_without_nul_unchecked(
        bytes: &[u8; N],
    ) -> Result<Self, InteriorNulError> {
        // SAFETY: `bytes` does not contain any 0 values as promised by the caller.
        let nonzero: &[NonZeroU8; N] = unsafe { &*bytes.as_ptr().cast() };
        Ok(Self {
            data: *nonzero,
            nul: Nul,
        })
    }

    /// Returns the fixed length.
    pub const fn len(&self) -> usize {
        N
    }

    /// Borrows this `CStrArray` as a `&CStr`.
    ///
    /// This is called by `Deref`.
    pub const fn as_c_str(&self) -> &CStr {
        // SAFETY:
        // - The first `N` bytes of `self` (`data` field) are kept non-nul.
        // - The last byte of `self` is always a nul byte.
        unsafe { CStr::from_bytes_with_nul_unchecked(self.as_bytes_with_nul()) }
    }

    /// Converts this C string to a byte array reference.
    ///
    /// The returned slice will not contain the trailing nul terminator
    /// that this C string has.
    pub const fn as_bytes(&self) -> &[u8; N] {
        // SAFETY: `[NonZeroU8; N]` has the same layout as `[u8; N]` and cannot be mutated through a reference.
        unsafe { &*self.data.as_ptr().cast() }
    }

    /// Converts this C string to a byte slice containing the trailing 0 byte.
    ///
    /// The length of the slice is `N + 1`.
    pub const fn as_bytes_with_nul(&self) -> &[u8] {
        // SAFETY:
        // - `Self` uses the `repr(C)` layout algorithm.
        // - The total size of `Self` is `N + 1`
        // - All bytes in `Self` are initialized.
        unsafe { slice::from_raw_parts(self as *const _ as *const u8, N + 1) }
    }

    /// Consumes `self` into its underlying array.
    pub const fn into_bytes(self) -> [u8; N] {
        *self.as_bytes()
    }

    /// Returns the fixed length.
    ///
    /// This uses the same name as [`CStr::count_bytes`] to prevent
    /// it from being called with `Deref`.
    #[deprecated = "use len"]
    pub const fn count_bytes(&self) -> usize {
        self.len()
    }

    /// Converts this C string to a byte slice.
    ///
    /// This uses the same name as [`CStr::to_bytes`] to prevent
    /// it from being called with `Deref`.
    #[deprecated = "use as_bytes"]
    pub const fn to_bytes(&self) -> &[u8] {
        self.as_bytes()
    }

    /// Converts this C string to a byte slice.
    ///
    /// This uses the same name as [`CStr::to_bytes_with_nul`] to prevent
    /// it from being called with `Deref`.
    #[deprecated = "use as_bytes_with_nul"]
    pub const fn to_bytes_with_nul(&self) -> &[u8] {
        self.as_bytes_with_nul()
    }
}

impl CStrArray<0> {
    /// Returns an empty `CStrArray`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::CStrArray;
    /// let s = CStrArray::empty();
    /// assert!(s.is_empty());
    /// ```
    pub const fn empty() -> Self {
        Self { data: [], nul: Nul }
    }
}

impl<const N: usize> Debug for CStrArray<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <CStr as Debug>::fmt(self.as_c_str(), f)
    }
}

impl<const N: usize> Deref for CStrArray<N> {
    type Target = CStr;

    fn deref(&self) -> &Self::Target {
        self.as_c_str()
    }
}

impl<const N: usize> AsRef<CStr> for CStrArray<N> {
    fn as_ref(&self) -> &CStr {
        self.as_c_str()
    }
}

impl<const N: usize> TryFrom<&CStr> for CStrArray<N> {
    type Error = CStrLenError<N>;

    fn try_from(val: &CStr) -> Result<Self, Self::Error> {
        Self::new(val)
    }
}

#[cfg(feature = "alloc")]
mod alloc {
    use super::*;
    use ::alloc::ffi::CString;

    impl<const N: usize> TryFrom<Box<CStr>> for CStrArray<N> {
        type Error = CStrLenError<N>;

        fn try_from(val: Box<CStr>) -> Result<Self, Self::Error> {
            Self::new(&val)
        }
    }

    impl<const N: usize> TryFrom<Rc<CStr>> for CStrArray<N> {
        type Error = CStrLenError<N>;

        fn try_from(val: Rc<CStr>) -> Result<Self, Self::Error> {
            Self::new(&val)
        }
    }

    impl<const N: usize> TryFrom<Arc<CStr>> for CStrArray<N> {
        type Error = CStrLenError<N>;

        fn try_from(val: Arc<CStr>) -> Result<Self, Self::Error> {
            Self::new(&val)
        }
    }

    impl<const N: usize> TryFrom<CString> for CStrArray<N> {
        type Error = CStrLenError<N>;

        fn try_from(val: CString) -> Result<Self, Self::Error> {
            Self::new(&val)
        }
    }

    impl<const N: usize> PartialEq<CString> for CStrArray<N> {
        fn eq(&self, other: &CString) -> bool {
            self.as_c_str() == other.as_c_str()
        }
    }

    impl<const N: usize> PartialEq<CStrArray<N>> for CString {
        fn eq(&self, other: &CStrArray<N>) -> bool {
            self.as_c_str() == other.as_c_str()
        }
    }
}

impl<const N: usize> PartialEq<CStr> for CStrArray<N> {
    fn eq(&self, other: &CStr) -> bool {
        self.as_c_str() == other
    }
}

impl<const N: usize> PartialEq<CStrArray<N>> for CStr {
    fn eq(&self, other: &CStrArray<N>) -> bool {
        self == other.as_c_str()
    }
}

impl<const N: usize> PartialEq<&CStr> for CStrArray<N> {
    fn eq(&self, other: &&CStr) -> bool {
        self.as_c_str() == *other
    }
}

impl<const N: usize> PartialEq<CStrArray<N>> for &CStr {
    fn eq(&self, other: &CStrArray<N>) -> bool {
        *self == other.as_c_str()
    }
}

/// Internal utility struct used by `cstr_array!`.
pub struct CStrArrayBytes<T>(pub T);

/// Builds a `CStrArray<N>` from `bytes` without nul, panicking on failure.
pub const fn build_cstr<const N: usize>(bytes: &[u8]) -> CStrArray<N> {
    let as_array: &[u8; N] = if bytes.len() == N {
        // SAFETY: `self.0.len() == N`
        unsafe { &*bytes.as_ptr().cast() }
    } else {
        CStrLenError::<N> {
            src_len: bytes.len(),
        }
        .const_panic()
    };
    match CStrArray::from_bytes_without_nul(as_array) {
        Ok(x) => x,
        Err(e) => e.const_panic(),
    }
}

impl<'a, const N: usize> CStrArrayBytes<&'a [u8; N]> {
    /// Unsizes the byte array
    pub const fn get(self) -> &'a [u8] {
        self.0
    }
}

impl<'a> CStrArrayBytes<&'a [u8]> {
    /// Copies the slice
    pub const fn get(self) -> &'a [u8] {
        self.0
    }
}

impl<'a> CStrArrayBytes<&'a str> {
    /// Gets the bytes of the `str`
    pub const fn get(self) -> &'a [u8] {
        self.0.as_bytes()
    }
}

impl<'a> CStrArrayBytes<&'a CStr> {
    /// Gets the bytes of the `CStr`, counting up to the nul terminator
    pub const fn get(self) -> &'a [u8] {
        // Using `CStr::to_bytes` bumps the MSRV higher than desired.
        // SAFETY: `count_bytes` returns the number of bytes that are present before the nul character.
        unsafe { slice::from_raw_parts(self.0.as_ptr().cast(), count_bytes(self.0)) }
    }
}

/// Builds [`CStrArray`] from constant strings of various types.
///
/// This macro can construct a `CStrArray<N>` from a constant expression of any of these input types:
///
/// - `&CStr`
/// - `&str`
/// - `&[u8]`
/// - `&[u8; N]`
///
/// This performs the necessary nul presence checks at compile time.
///
/// # Examples
///
/// Pass a `const` expression of `&CStr` to build a `CStrArray` with the same length.
///
/// ```
/// # use core::ffi::CStr;
/// # use str_array::cstr_array;
/// let x = cstr_array!(c"Buzz");
/// assert_eq!(x.len(), 4);
///
/// const NAME: &CStr = c"Sally";
/// let y = cstr_array!(NAME);
/// assert_eq!(y, c"Sally");
/// ```
///
/// Pass a `const` expression of `&str` or `&[u8]` to build a `CStrArray` with the same length.
/// A nul terminator is appended automatically.
///
/// ```
/// # use core::ffi::CStr;
/// # use str_array::cstr_array;
/// assert_eq!(cstr_array!("Buzz"), cstr_array!(b"Buzz"));
/// ```
///
/// It's a compile-time failure to invoke `cstr_array!` with a nul inside the string.
///
/// ```compile_fail
/// # use core::ffi::CStr;
/// # use str_array::cstr_array;
/// _ = cstr_array!("nul is appended by the macro; don't include it\0");
/// ```
///
/// ```compile_fail
/// # use core::ffi::CStr;
/// # use str_array::cstr_array;
/// _ = cstr_array!(b"nul\0in the middle");
/// ```
///
/// Define `static` or `const` items by eliding the type.
///
/// The length of the `CStrArray` uses the length of the assigned string.
/// Note that the assignment expression currently is evaluated twice,
/// but this should have no effect due to it being in `const`.
///
/// ```
/// # use core::ptr::addr_of;
/// # use str_array::{cstr_array, CStrArray};
/// const BYTE_ARRAY: [u8; 12] = *b"direct array";
///
/// cstr_array! {
///     static STATIC = c"static";
///     static mut STATIC_MUT = c"static_mut";
///     const CONST = c"constant";
///
///     static FROM_STR = concat!("checked", " for ", "nul");
///     static FROM_BYTES_REF = b"also checked for nul";
///     static FROM_BYTES_ARRAY = &BYTE_ARRAY;  // doesn't construct directly from array
/// }
///
/// assert_eq!(STATIC, c"static");
/// assert_eq!(unsafe { &*addr_of!(STATIC_MUT) }, c"static_mut");
/// assert_eq!(CONST, c"constant");
///
/// assert_eq!(FROM_STR, c"checked for nul");
/// assert_eq!(FROM_BYTES_REF, c"also checked for nul");
/// assert_eq!(FROM_BYTES_ARRAY, *c"direct array");
/// ```
// TODO: Support plain string literals too (requires a nul check).
// TODO: maybe just write `static STATIC = c"static"`
#[macro_export]
macro_rules! cstr_array {
    // TODO: same caveats as str_array
    (@impl item
        ($([$attr:meta])*)
        ($($item_kind:tt)*)
        $name:ident = $val:expr; $($rest:tt)*
    ) => {
        $(#[$attr])* $($item_kind)* $name: $crate::CStrArray<{ $crate::__internal::CStrArrayBytes($val).get().len() }> =
            $crate::__internal::build_cstr($crate::__internal::CStrArrayBytes($val).get());
        $crate::cstr_array!($($rest)*)
    };
    ($(#[$attr:meta])* static mut $($rest:tt)*) => {
        $crate::cstr_array!(@impl item ($([$attr])*) (static mut) $($rest)*);
    };
    ($(#[$attr:meta])* static $($rest:tt)*) => {
        $crate::cstr_array!(@impl item ($([$attr])*) (static) $($rest)*);
    };
    ($(#[$attr:meta])* const $($rest:tt)*) => {
        $crate::cstr_array!(@impl item ($([$attr])*) (const) $($rest)*);
    };
    ($val:expr) => {{
        const VAL: &[u8] = $crate::__internal::CStrArrayBytes($val).get();
        const ARRAY: $crate::CStrArray<{ VAL.len() }> = $crate::__internal::build_cstr(VAL);
        ARRAY
    }};
    () => {};
}
