use core::{
    ffi::{c_char, CStr},
    fmt::{self, Debug},
    num::NonZeroU8,
    ops::{Deref, DerefMut},
    slice,
};

use crate::{
    const_mut_fn,
    error::{CStrLenError, InteriorNulError},
};
use NulByte::Nul;

/// A byte that must always be 0.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[repr(u8)]
enum NulByte {
    Nul = 0,
}

/// The same as `val.count_bytes()` but is `const` on low MSRV
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

/// Fixed-size [`CStr`], backed by an array.
///
/// The length `N` is the number of bytes in the string _not_ including the nul terminator.
///
/// Because it has a fixed size, it can be put directly in a `static` and all
/// casting operations are constant-time.
///
/// # Examples
///
/// Small C strings of fixed size:
///
/// ```
/// # use str_array::cstr_array;
/// let mut airports = [
///     cstr_array!("JFK"), cstr_array!("LAX"),
///     cstr_array!("LHR"), cstr_array!("CDG"),
///     cstr_array!("HND"), cstr_array!("PEK"),
///     cstr_array!("DXB"), cstr_array!("AMS"),
///     cstr_array!("FRA"), cstr_array!("SIN"),
/// ];
///
/// // All of the C strings are contiguous in memory.
/// assert_eq!(core::mem::size_of_val(&airports), 40);
///
/// airports.sort();
/// assert_eq!(airports[0], c"AMS");
/// ```
///
/// Storing `CStr` contents directly in a `static`:
///
/// ```
/// # use core::mem::size_of_val;
/// # use str_array::cstr_array;
/// cstr_array! {
///     static FOO = b"Hello, world!";
///     static mut FOO_MUT = c"c string buffer";
/// }
/// assert_eq!(&FOO, c"Hello, world!");
/// assert_eq!(size_of_val(&FOO), 14);
/// let foo_mut = unsafe { &mut *&raw mut FOO_MUT };
/// foo_mut.data[0] = b'C'.try_into().unwrap();
/// assert_eq!(foo_mut, c"C string buffer");
/// assert_eq!(size_of_val(foo_mut), 16);
/// ```
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[repr(C)]
pub struct CStrArray<const N: usize> {
    /// The non-nul data in this C string.
    pub data: [NonZeroU8; N],
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
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::ffi::CString;
    /// # use str_array::CStrArray;
    /// let cstring = CString::new(format!("he{}", "llo")).unwrap();
    /// let s = CStrArray::<5>::new(&cstring).unwrap();
    /// assert_eq!(s, c"hello");
    ///
    /// assert!(CStrArray::<5>::new(c"foo").is_err());
    /// ```
    ///
    /// [`cstr_array!`]: crate::cstr_array
    pub const fn new(val: &CStr) -> Result<Self, CStrLenError<N>> {
        let src_len = count_bytes(val);
        if src_len != N {
            return Err(CStrLenError { src_len });
        }
        // SAFETY: `val` is checked to point to `N` non-nul bytes followed by a nul.
        Ok(unsafe { Self::new_unchecked(val) })
    }

    /// Builds a `StrArray<N>` from `val` without a size check.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::CStrArray;
    /// // SAFETY: c"hello".count_bytes() == 5
    /// let s = unsafe { CStrArray::<5>::new_unchecked(c"hello") };
    /// assert_eq!(s, c"hello");
    /// ```
    ///
    /// # Safety
    ///
    /// `val.count_bytes() == N` or else behavior is undefined.
    pub const unsafe fn new_unchecked(val: &CStr) -> Self {
        CStrArray {
            data: unsafe { *val.as_ptr().cast() },
            nul: Nul,
        }
    }

    /// Converts a `&CStr` to a `&CStrArray<N>` with a length check.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::ffi::CString;
    /// # use str_array::CStrArray;
    /// let s: &CStrArray<5> = CStrArray::ref_from_c_str(c"hello").unwrap();
    /// assert_eq!(s, c"hello");
    ///
    /// assert!(CStrArray::<5>::ref_from_c_str(c"foo").is_err());
    /// ```
    pub const fn ref_from_c_str(val: &CStr) -> Result<&Self, CStrLenError<N>> {
        let src_len = count_bytes(val);
        if src_len != N {
            return Err(CStrLenError { src_len });
        }
        // SAFETY: `val.count_bytes() == N`
        Ok(unsafe { Self::ref_from_c_str_unchecked(val) })
    }

    /// Converts a `&CStr` to a `&CStrArray<N>` without a length check.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::CStrArray;
    /// // SAFETY: c"abc".count_bytes() == 3
    /// let s: &CStrArray<3> = unsafe {
    ///     CStrArray::ref_from_c_str_unchecked(c"abc")
    /// };
    /// assert_eq!(s.into_bytes(), [b'a', b'b', b'c']);
    /// ```
    ///
    /// # Safety
    ///
    /// `val.count_bytes() == N` or else behavior is undefined.
    pub const unsafe fn ref_from_c_str_unchecked(val: &CStr) -> &Self {
        // SAFETY:
        // - The caller promises the string is `N` bytes long.
        // - `CStr` thus promises that `as_ptr` points to `N` non-zero bytes
        //   followed by a zero byte--the layout and bit validity of `Self`.
        unsafe { &*val.as_ptr().cast() }
    }

    const_mut_fn! {
        /// Converts a `&mut CStr` to a `&mut CStrArray<N>` with a length check.
        ///
        /// # Examples
        ///
        /// ```
        /// # use std::ffi::CString;
        /// # use str_array::CStrArray;
        /// let mut boxed = CString::new("hello").unwrap().into_boxed_c_str();
        /// let s_mut = CStrArray::<5>::mut_from_c_str(&mut boxed).unwrap();
        /// s_mut.data[0] = b'H'.try_into().unwrap();
        /// assert_eq!(&*boxed, c"Hello");
        ///
        /// let mut short = CString::new("foo").unwrap().into_boxed_c_str();
        /// assert!(CStrArray::<5>::mut_from_c_str(&mut short).is_err());
        /// ```
        pub fn mut_from_c_str(val: &mut CStr) -> Result<&mut Self, CStrLenError<N>> {
            let src_len = count_bytes(val);
            if src_len != N {
                return Err(CStrLenError { src_len });
            }
            // SAFETY: `val.count_bytes() == N`
            Ok(unsafe { Self::mut_from_c_str_unchecked(val) })
        }
    }

    const_mut_fn! {
        /// Converts a `&mut CStr` to a `&mut CStrArray<N>` without a length check.
        ///
        /// # Examples
        ///
        /// ```
        /// # use std::ffi::CString;
        /// # use str_array::CStrArray;
        /// let mut boxed = CString::new("abc").unwrap().into_boxed_c_str();
        ///
        /// // SAFETY: boxed.count_bytes() == 3
        /// let m: &mut CStrArray<3> = unsafe {
        ///     CStrArray::mut_from_c_str_unchecked(&mut boxed)
        /// };
        /// m.data[0] = b'A'.try_into().unwrap();
        /// assert_eq!(&*boxed, c"Abc");
        /// ```
        ///
        /// # Safety
        ///
        /// `val.count_bytes() == N` or else behavior is undefined.
        pub unsafe fn mut_from_c_str_unchecked(val: &mut CStr) -> &mut Self {
            // SAFETY:
            // - The caller promises the string is `N` bytes long.
            // - `CStr` thus promises that `as_ptr` points to `N` non-zero bytes
            //   followed by a zero byte--the layout and bit validity of `Self`.
            unsafe { &mut *(val as *mut CStr as *mut Self) }
        }
    }

    /// Constructs a `CStrArray<N>` from an array with its byte contents.
    ///
    /// Note that `bytes` should _not_ include the nul terminator -
    /// it is appended automatically by this method.
    ///
    /// If `val` is a literal or `const`, consider using [`cstr_array!`]
    /// instead, which checks for the presence of a nul at compile time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::CStrArray;
    /// let s = CStrArray::from_bytes_without_nul(b"hello").unwrap();
    /// assert_eq!(s, c"hello");
    ///
    /// let bytes_with_nul = b"he\0lo";
    /// assert!(CStrArray::from_bytes_without_nul(bytes_with_nul).is_err());
    /// ```
    ///
    /// [`cstr_array!`]: crate::cstr_array
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
        Ok(unsafe { Self::from_bytes_without_nul_unchecked(bytes) })
    }

    /// Constructs a `CStrArray<N>` from an array with its byte contents and no checks.
    ///
    /// Note that this does _not_ include the nul terminator -
    /// it is appended automatically.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::CStrArray;
    /// // SAFETY: b"hello" contains no nul bytes
    /// let s = unsafe { CStrArray::from_bytes_without_nul_unchecked(b"hello") };
    /// assert_eq!(s, c"hello");
    /// ```
    ///
    /// # Safety
    ///
    /// `bytes` must not have any 0 (nul) bytes.
    pub const unsafe fn from_bytes_without_nul_unchecked(bytes: &[u8; N]) -> Self {
        // SAFETY: `bytes` does not contain any 0 values as promised by the caller.
        let nonzero: &[NonZeroU8; N] = unsafe { &*bytes.as_ptr().cast() };
        Self {
            data: *nonzero,
            nul: Nul,
        }
    }

    /// Returns the fixed length.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::cstr_array;
    /// let s = cstr_array!(c"hello");
    /// assert_eq!(s.len(), 5);
    /// ```
    #[allow(clippy::len_without_is_empty)]
    pub const fn len(&self) -> usize {
        N
    }

    /// Borrows this `CStrArray` as a `&CStr`.
    ///
    /// This is called by `Deref` automatically.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::cstr_array;
    /// let s = cstr_array!(c"hello");
    /// assert_eq!(s.as_c_str().to_str().unwrap(), "hello");
    /// assert_eq!(s.to_str().unwrap(), "hello");  // using deref
    /// ```
    pub const fn as_c_str(&self) -> &CStr {
        // SAFETY:
        // - The first `N` bytes of `self` (`data` field) are kept non-nul.
        // - The last byte of `self` is always a nul byte.
        unsafe { CStr::from_bytes_with_nul_unchecked(self.as_bytes_with_nul()) }
    }

    const_mut_fn! {
        /// Borrows this `CStrArray` as a `&mut CStr`.
        ///
        /// This is called by `DerefMut` automatically.
        ///
        /// While `&mut CStr` is currently undersupported in the standard library,
        /// it can be safely constructed by borrowing a `Box<CStr>` and `unsafe` code
        /// can utilize its invariants.
        ///
        /// # Examples
        ///
        /// ```
        /// # use core::{ffi::CStr, ptr};
        /// # use str_array::cstr_array;
        /// fn make_c_str_ascii_uppercase(x: &mut CStr) {
        ///     let mut p: *mut u8 = ptr::from_mut(x).cast();
        ///     loop {
        ///         // SAFETY: the last byte of `CStr` is 0
        ///         let b = unsafe { &mut *p };
        ///         match *b {
        ///             0 => return,
        ///             b'a'..=b'z' => *b -= 32,
        ///             _ => {}
        ///         }
        ///         // SAFETY: the end of the `CStr` has not been reached
        ///         p = unsafe { p.add(1) };
        ///     }
        /// }
        ///
        /// let mut s = cstr_array!(c"hello");
        /// make_c_str_ascii_uppercase(s.as_mut_c_str());  // or just `&mut s`
        /// assert_eq!(s, c"HELLO");
        /// ```
        pub fn as_mut_c_str(&mut self) -> &mut CStr {
            // This is carefully crafted to manually construct a `&mut CStr` for now and the future
            // when a dedicated method like `from_mut_bytes_with_nul_unchecked` is added.
            // It should handle `&mut CStr` as wide (slice-based) as it is today and its thin future.
            // The length pointer metadata is preserved when `as`-casting between raw
            // slice-DST pointers, and dropped when casting to a thin pointer.
            // As of writing on nightly, it is valid to cast `*mut [u8]` to `*mut ExternType`,
            // dropping the metadata as when casting to a pointer-to-`Sized`.
            // This code bets that when `extern type` is stabilized and `CStr` is switched over
            // to use it that this will remain true and valid.
            let as_slice: *mut [c_char] = core::ptr::slice_from_raw_parts_mut(self.as_mut_ptr(), N + 1);

            // SAFETY:
            // - The first `N` bytes of `self` (`data` field) are kept non-nul.
            // - The last byte of `self` is always a nul byte.
            // - The layout of `CStr` is `repr(transparent)` over `[c_char]`
            //   including the nul, or an extern Type.
            //   This slice length inherently must include the `nul` byte and no more.
            unsafe { &mut *(as_slice as *mut CStr) }
        }
    }

    /// Converts this C string to a byte array reference.
    ///
    /// The returned slice will not contain the trailing nul terminator
    /// that this C string has.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::cstr_array;
    /// let x = cstr_array!(c"Hello");
    /// let &[a, b @ .., c] = x.as_bytes();
    /// assert_eq!(a, b'H');
    /// assert_eq!(b, *b"ell");
    /// assert_eq!(c, b'o');
    /// ```
    pub const fn as_bytes(&self) -> &[u8; N] {
        // SAFETY: `[NonZeroU8; N]` has the same layout as `[u8; N]` and cannot be mutated through a reference.
        unsafe { &*self.data.as_ptr().cast() }
    }

    /// Converts this C string to a `&[NonZero<u8>]`.
    ///
    /// This is also exposed in `self.data`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::cstr_array;
    /// let s = cstr_array!(c"hello");
    /// let bytes = s.as_nonzero_bytes();
    /// assert_eq!(bytes.len(), 5);
    /// assert_eq!(bytes[0].get(), b'h');
    /// ```
    pub const fn as_nonzero_bytes(&self) -> &[NonZeroU8; N] {
        &self.data
    }

    const_mut_fn! {
        /// Converts this C string to a `&mut [NonZero<u8>]`.
        ///
        /// This allows for safe in-place mutation of the C string contents
        /// without changing its length.
        ///
        /// This is also exposed in `self.data`.
        ///
        /// # Examples
        ///
        /// ```
        /// # use str_array::cstr_array;
        /// let mut s = cstr_array!(c"hello");
        /// s.as_mut_nonzero_bytes()[0] = b'H'.try_into().unwrap();
        /// assert_eq!(s, c"Hello");
        /// ```
        pub fn as_mut_nonzero_bytes(&mut self) -> &mut [NonZeroU8; N] {
            &mut self.data
        }
    }

    /// Converts this C string to a byte slice containing the trailing 0 byte.
    ///
    /// The length of the slice is `N + 1`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::cstr_array;
    /// let s = cstr_array!(c"hello");
    /// assert_eq!(s.as_bytes_with_nul(), b"hello\0");
    /// assert_eq!(s.as_bytes_with_nul().len(), 6);
    /// ```
    pub const fn as_bytes_with_nul(&self) -> &[u8] {
        // SAFETY:
        // - `Self` uses the `repr(C)` layout algorithm.
        // - The total size of `Self` is `N + 1`
        // - All bytes in `Self` are initialized.
        unsafe { slice::from_raw_parts(self as *const _ as *const u8, N + 1) }
    }

    const_mut_fn! {
        /// Returns the mutable inner pointer to this C string.
        ///
        /// The returned pointer will be valid for as long as `self` is,
        /// and points to a contiguous region of memory terminated with
        /// a 0 byte to represent the end of the string.
        ///
        /// The type of the returned pointer is `*mut c_char`, and whether
        /// it’s an alias for `*mut i8` or `*mut u8` is platform-specific.
        ///
        /// **WARNING**
        ///
        /// The returned pointer can be mutated through, but certain constraints
        /// must be upheld:
        ///
        /// - It is your responsibility to make sure that the underlying memory
        ///   is not freed too early.
        /// - The nul terminator cannot be relocated to earlier in the string.
        ///   In other words, the length of the C string cannot be changed.
        ///   This restriction can never be loosened, as the first `N` bytes
        ///   of `self` are required to have non-zero contents.
        ///
        /// # Examples
        ///
        /// ```
        /// # use str_array::cstr_array;
        /// let mut s = cstr_array!("hello");
        /// unsafe { s.as_mut_ptr().cast::<u8>().write(b'J') }
        /// assert_eq!(s, c"Jello");
        /// ```
        pub fn as_mut_ptr(&mut self) -> *mut c_char {
            self as *mut Self as *mut c_char
        }
    }

    /// Consumes `self` into its underlying array.
    ///
    /// # Examples
    ///
    /// ```
    /// # use str_array::cstr_array;
    /// let x = cstr_array!(c"Fizzy");
    ///
    /// let [a, b @ .., c] = x.into_bytes();
    /// assert_eq!(a, b'F');
    /// assert_eq!(b, *b"izz");
    /// assert_eq!(c, b'y');
    /// ```
    pub const fn into_bytes(self) -> [u8; N] {
        *self.as_bytes()
    }

    /// Returns the fixed length.
    ///
    /// This uses the same name as [`CStr::count_bytes`] to prevent
    /// it from being called with `Deref`.
    #[deprecated = "use `len`"]
    pub const fn count_bytes(&self) -> usize {
        self.len()
    }

    /// Converts this C string to a byte slice.
    ///
    /// This uses the same name as [`CStr::to_bytes`] to prevent
    /// it from being called with `Deref`.
    #[deprecated = "use `as_bytes`"]
    pub const fn to_bytes(&self) -> &[u8] {
        self.as_bytes()
    }

    /// Converts this C string to a byte slice.
    ///
    /// This uses the same name as [`CStr::to_bytes_with_nul`] to prevent
    /// it from being called with `Deref`.
    #[deprecated = "use `as_bytes_with_nul`"]
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

impl<const N: usize> DerefMut for CStrArray<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_c_str()
    }
}

impl<const N: usize> AsRef<CStr> for CStrArray<N> {
    fn as_ref(&self) -> &CStr {
        self.as_c_str()
    }
}

impl<const N: usize> AsMut<CStr> for CStrArray<N> {
    fn as_mut(&mut self) -> &mut CStr {
        self.as_mut_c_str()
    }
}

impl<const N: usize> TryFrom<&CStr> for CStrArray<N> {
    type Error = CStrLenError<N>;

    fn try_from(val: &CStr) -> Result<Self, Self::Error> {
        Self::new(val)
    }
}

impl<const N: usize> TryFrom<&[u8; N]> for CStrArray<N> {
    type Error = InteriorNulError;

    fn try_from(val: &[u8; N]) -> Result<Self, Self::Error> {
        // Reuse existing constructor which checks for interior nul bytes.
        CStrArray::from_bytes_without_nul(val)
    }
}

impl<const N: usize> From<CStrArray<N>> for [u8; N] {
    fn from(val: CStrArray<N>) -> Self {
        val.into_bytes()
    }
}

impl<const N: usize> From<CStrArray<N>> for [NonZeroU8; N] {
    fn from(val: CStrArray<N>) -> Self {
        val.data
    }
}

impl<const N: usize> From<[NonZeroU8; N]> for CStrArray<N> {
    fn from(data: [NonZeroU8; N]) -> Self {
        Self { data, nul: Nul }
    }
}

impl<const N: usize> AsRef<[NonZeroU8]> for CStrArray<N> {
    fn as_ref(&self) -> &[NonZeroU8] {
        self.as_nonzero_bytes()
    }
}

impl<const N: usize> AsRef<[NonZeroU8; N]> for CStrArray<N> {
    fn as_ref(&self) -> &[NonZeroU8; N] {
        self.as_nonzero_bytes()
    }
}

impl<const N: usize> AsMut<[NonZeroU8]> for CStrArray<N> {
    fn as_mut(&mut self) -> &mut [NonZeroU8] {
        self.as_mut_nonzero_bytes()
    }
}

impl<const N: usize> AsMut<[NonZeroU8; N]> for CStrArray<N> {
    fn as_mut(&mut self) -> &mut [NonZeroU8; N] {
        self.as_mut_nonzero_bytes()
    }
}

impl<const N: usize> AsRef<[u8]> for CStrArray<N> {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<const N: usize> AsRef<[u8; N]> for CStrArray<N> {
    fn as_ref(&self) -> &[u8; N] {
        self.as_bytes()
    }
}

impl<'a, const N: usize> TryFrom<&'a CStr> for &'a CStrArray<N> {
    type Error = CStrLenError<N>;

    fn try_from(val: &'a CStr) -> Result<&'a CStrArray<N>, Self::Error> {
        CStrArray::ref_from_c_str(val)
    }
}

impl<'a, const N: usize> TryFrom<&'a mut CStr> for &'a mut CStrArray<N> {
    type Error = CStrLenError<N>;

    fn try_from(val: &'a mut CStr) -> Result<&'a mut CStrArray<N>, Self::Error> {
        CStrArray::mut_from_c_str(val)
    }
}

impl<'a, const N: usize> From<&'a CStrArray<N>> for &'a CStr {
    fn from(val: &'a CStrArray<N>) -> Self {
        val.as_c_str()
    }
}

impl<'a, const N: usize> From<&'a mut CStrArray<N>> for &'a mut CStr {
    fn from(val: &'a mut CStrArray<N>) -> Self {
        val.as_mut_c_str()
    }
}

#[cfg(feature = "alloc")]
mod alloc {
    use crate::{error::CStrLenError, CStrArray};
    use ::alloc::{boxed::Box, ffi::CString, rc::Rc, sync::Arc};
    use core::ffi::CStr;

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

    impl<const N: usize> From<CStrArray<N>> for CString {
        fn from(val: CStrArray<N>) -> Self {
            // `as_bytes()` is guaranteed to contain no interior nul bytes.
            CString::from(val.as_c_str())
        }
    }

    impl<const N: usize> From<CStrArray<N>> for Box<CStr> {
        fn from(val: CStrArray<N>) -> Self {
            Box::from(val.as_c_str())
        }
    }

    impl<const N: usize> From<CStrArray<N>> for Rc<CStr> {
        fn from(val: CStrArray<N>) -> Self {
            Rc::from(val.as_c_str())
        }
    }

    impl<const N: usize> From<CStrArray<N>> for Arc<CStr> {
        fn from(val: CStrArray<N>) -> Self {
            Arc::from(val.as_c_str())
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
// TODO: maybe just write `static STATIC = cstr!("static")`
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

#[cfg(test)]
macro_rules! cstr {
    ($x:literal) => {
        match core::ffi::CStr::from_bytes_with_nul(concat!($x, "\0").as_bytes()) {
            Ok(x) => x,
            Err(_) => panic!(),
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    use ::alloc::format;

    #[test]
    fn test_new() {
        let cstr = cstr!("hello");
        let cstr_array = CStrArray::<5>::new(cstr).unwrap();
        assert_eq!(cstr_array.as_c_str(), cstr);
        assert_eq!(cstr_array.len(), 5);
        assert!(!cstr_array.is_empty());

        let cstr_long = cstr!("hellos");
        let err = CStrArray::<5>::new(cstr_long).unwrap_err();
        assert_eq!(err.src_len, 6);

        let cstr_short = cstr!("hell");
        let err = CStrArray::<5>::new(cstr_short).unwrap_err();
        assert_eq!(err.src_len, 4);
    }

    #[test]
    fn test_from_bytes_without_nul() {
        let bytes = b"hello";
        let cstr_array = CStrArray::from_bytes_without_nul(bytes).unwrap();
        assert_eq!(cstr_array.as_bytes(), bytes);

        let bytes_with_nul = b"he\0llo";
        let err = CStrArray::from_bytes_without_nul(bytes_with_nul).unwrap_err();
        assert_eq!(err.position, 2);
    }

    #[test]
    fn test_empty() {
        let empty = CStrArray::<0>::empty();
        assert!(empty.is_empty());
        assert_eq!(empty.len(), 0);
        assert_eq!(empty.as_c_str(), <&CStr>::default());
    }

    #[test]
    fn test_debug() {
        let cstr_array = CStrArray::from_bytes_without_nul(b"hello").unwrap();
        let s = format!("{:?}", cstr_array);
        assert_eq!(s, r#""hello""#);
    }

    #[test]
    fn test_as_bytes_with_nul() {
        let cstr_array = CStrArray::from_bytes_without_nul(b"hello").unwrap();
        assert_eq!(cstr_array.as_bytes_with_nul(), b"hello\0");
    }

    #[test]
    fn test_into_bytes() {
        let cstr_array = CStrArray::from_bytes_without_nul(b"hello").unwrap();
        assert_eq!(cstr_array.into_bytes(), *b"hello");
    }

    #[test]
    fn test_try_from_cstr() {
        let cstr = cstr!("hello");
        let cstr_array = CStrArray::<5>::try_from(cstr).unwrap();
        assert_eq!(cstr_array.as_c_str(), cstr);

        let cstr_long = cstr!("hellos");
        let err = CStrArray::<5>::try_from(cstr_long).unwrap_err();
        assert_eq!(err.src_len, 6);
    }

    #[test]
    fn test_partial_eq() {
        let cstr_array = CStrArray::from_bytes_without_nul(b"hello").unwrap();
        let cstr = cstr!("hello");
        assert_eq!(&cstr_array, cstr);
        assert_eq!(cstr, &cstr_array);
        assert_eq!(&cstr_array, &cstr);
        assert_eq!(&cstr, &cstr_array);
    }

    #[test]
    fn test_macro() {
        let cstr_array = cstr_array!(cstr!("hello"));
        assert_eq!(cstr_array.len(), 5);
        assert_eq!(cstr_array, cstr!("hello"));

        let str_array = cstr_array!("hello");
        assert_eq!(str_array.len(), 5);
        assert_eq!(str_array, cstr!("hello"));

        let bytes_array = cstr_array!(b"hello");
        assert_eq!(bytes_array.len(), 5);
        assert_eq!(bytes_array, cstr!("hello"));
    }

    #[test]
    #[deny(non_upper_case_globals)]
    fn test_macro_items() {
        cstr_array! {
            static STATIC = cstr!("hello");
            const CONST = "world";
        }
        assert_eq!(STATIC.len(), 5);
        assert_eq!(STATIC, cstr!("hello"));
        assert_eq!(CONST.len(), 5);
        assert_eq!(CONST, cstr!("world"));
    }

    #[test]
    fn test_from_into_bytes() {
        let cstr_array = CStrArray::from_bytes_without_nul(b"hello").unwrap();
        let bytes: [u8; 5] = cstr_array.into();
        assert_eq!(bytes, *b"hello");
    }

    #[test]
    fn test_from_into_nonzero_bytes() {
        let cstr_array = CStrArray::from_bytes_without_nul(b"hello").unwrap();
        let nonzero: [NonZeroU8; 5] = cstr_array.into();
        assert_eq!(nonzero[0].get(), b'h');
        assert_eq!(nonzero[4].get(), b'o');

        let cstr_array2 = CStrArray::from(nonzero);
        assert_eq!(cstr_array2, cstr!("hello"));
    }

    #[test]
    fn test_from_ref_cstr_array() {
        let cstr_array = CStrArray::from_bytes_without_nul(b"hello").unwrap();
        let cstr_ref: &CStr = (&cstr_array).into();
        assert_eq!(cstr_ref, cstr!("hello"));
    }

    #[test]
    fn test_from_mut_ref_cstr_array() {
        let mut cstr_array = CStrArray::from_bytes_without_nul(b"hello").unwrap();
        let cstr_mut: &mut CStr = (&mut cstr_array).into();
        // Modify through the mutable CStr reference
        unsafe {
            let ptr = cstr_mut as *mut CStr as *mut u8;
            *ptr = b'H';
        }
        assert_eq!(cstr_array, cstr!("Hello"));
    }

    #[test]
    fn test_as_mut_cstr() {
        let mut cstr_array = CStrArray::from_bytes_without_nul(b"hello").unwrap();
        let cstr_mut: &mut CStr = cstr_array.as_mut();
        unsafe {
            let ptr = cstr_mut as *mut CStr as *mut u8;
            *ptr = b'J';
        }
        assert_eq!(cstr_array, cstr!("Jello"));
    }
}

#[cfg(all(test, feature = "alloc"))]
mod alloc_tests {
    use super::*;

    use ::alloc::{boxed::Box, ffi::CString, rc::Rc, sync::Arc};

    #[test]
    fn test_try_from_alloc() {
        let cstr = cstr!("hello");
        let cstring = CString::new("hello").unwrap();

        let from_box = CStrArray::<5>::try_from(Box::from(cstr)).unwrap();
        assert_eq!(from_box, cstr);

        let from_rc = CStrArray::<5>::try_from(Rc::from(cstr)).unwrap();
        assert_eq!(from_rc, cstr);

        let from_arc = CStrArray::<5>::try_from(Arc::from(cstr)).unwrap();
        assert_eq!(from_arc, cstr);

        let from_cstring = CStrArray::<5>::try_from(cstring.clone()).unwrap();
        assert_eq!(from_cstring, cstr);
    }

    #[test]
    fn test_partial_eq_alloc() {
        let cstr_array = CStrArray::from_bytes_without_nul(b"hello").unwrap();
        let cstring = CString::new("hello").unwrap();
        assert_eq!(cstr_array, *cstring);
        assert_eq!(*cstring, cstr_array);
    }
}
