/// Wraps a _single function_ to be a `const` mut fn.
///
/// The `build.rs` checks if `&mut` works in `const` to enable `cfg(has_const_mut)`.
#[cfg(has_const_mut)]
macro_rules! const_mut_fn {
    ($(#[$m:meta])* $vis:vis unsafe fn $($rest:tt)*) => {
        $(#[$m])*
        ///
        /// # `const` support
        ///
        /// This function is `const` if `&mut` is supported in `const`.
        #[allow(clippy::incompatible_msrv)]
        $vis const unsafe fn $($rest)*
    };
    ($(#[$m:meta])* $vis:vis fn $($rest:tt)*) => {
        $(#[$m])*
        ///
        /// # `const` support
        ///
        /// This function is `const` if `&mut` is supported in `const`.
        #[allow(clippy::incompatible_msrv)]
        $vis const fn $($rest)*
    };
}

/// The `build.rs` checks if `&mut` works in `const` to enable `cfg(has_const_mut)`.
#[cfg(not(has_const_mut))]
macro_rules! const_mut_fn {
    ($(#[$m:meta])* $vis:vis unsafe fn $($rest:tt)*) => {
        $(#[$m])*
        ///
        /// # `const` support
        ///
        /// This function is `const` if `&mut` is supported in `const`.
        $vis unsafe fn $($rest)*
    };
    ($(#[$m:meta])* $vis:vis fn $($rest:tt)*) => {
        $(#[$m])*
        ///
        /// # `const` support
        ///
        /// This function is `const` if `&mut` is supported in `const`.
        $vis fn $($rest)*
    };
}

pub(crate) use const_mut_fn;
