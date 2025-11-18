# str_array

![License: Apache-2.0 OR MIT](https://img.shields.io/badge/license-Apache--2.0%20OR%20MIT-blue) [![str_array on crates.io](https://img.shields.io/crates/v/str_array)](https://crates.io/crates/str_array) [![str_array on docs.rs](https://docs.rs/str_array/badge.svg)](https://docs.rs/str_array) [![Source Code Repository](https://img.shields.io/badge/Code-On%20GitHub-blue?logo=GitHub)](https://github.com/kupiakos/str-array) ![Rust Version: 1.64.0](https://img.shields.io/badge/rustc-1.64.0-orange.svg)

<!-- crate documentation start -->
Provides fixed-size string types [`StrArray`] and [`CStrArray`].

[`StrArray`] serves as the `str` equivalent of `[u8; N]`, offering a `Deref`
to `&str` and ensuring the UTF-8 invariant is always upheld, but with a
size known at compile time. This is designed for `no_std` environments
or where strings are always a certain size.

The [`str_array!`] macro provides a compile-time-checked way to
build [`StrArray`] values from string literals and constants.

Similarly, [`CStrArray`] and [`cstr_array!`] can construct a
nul-terminated [`CStr`](https://doc.rust-lang.org/core/ffi/c_str/struct.CStr.html) safely on the stack.

## Features

- `no_std` support - disable default features to use without `std`
- Optional `alloc` and `std` features
- Full `const` support
- [C string](https://docs.rs/str_array/0.2.0/str_array/struct.CStrArray.html) support

## Examples

```rust
use str_array::{str_array, StrArray};

// Create from a constant using the macro. The length is inferred.
let s1 = str_array!("hello");
assert_eq!(s1.len(), 5);
assert_eq!(s1, "hello");
assert!(matches!(s1.into_bytes(), [b'h', b'e', b'l', b'l', b'o']));

// Or create from a runtime &str with an length check.
let s2: StrArray<12> = StrArray::new(&format!("{s1}, world")).unwrap();
assert_eq!(core::mem::size_of_val(&s2), 12);
assert_eq!(s2, "hello, world");

// Or create from bytes with a UTF-8 check.
let s3 = StrArray::from_utf8(
    b"\xF0\x9F\xA4\x8C\xF0\x9F\x8F\xBC"
).unwrap();
assert_eq!(s3, "🤌🏼");

// Or define an item with an inferred length.
str_array! {
    static S4 = "Georgia";
}
assert_eq!(S4.len(), 7);
```

[`CStrArray`]: https://docs.rs/str_array/0.2.0/str_array/struct.CStrArray.html
[`StrArray`]: https://docs.rs/str_array/0.2.0/str_array/struct.StrArray.html
[`cstr_array!`]: https://docs.rs/str_array/0.2.0/str_array/macro.cstr_array.html
[`str_array!`]: https://docs.rs/str_array/0.2.0/str_array/macro.str_array.html

<!-- crate documentation end -->

## License

Licensed under either of the Apache 2.0 or MIT licenses.
