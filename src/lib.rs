//! A library for code formatting designed for ease of use.
//!
//! The [`Formattable`] trait is your primary entrypoint to this crate,
//! and it should be implemented for any value you want to do formatting on.
//!
//! See the code examples for examples of how to use this library.

#![warn(
  absolute_paths_not_starting_with_crate,
  redundant_imports,
  redundant_lifetimes,
  future_incompatible,
  deprecated_in_future,
  missing_copy_implementations,
  missing_debug_implementations,
  missing_docs,
  unnameable_types,
  unreachable_pub
)]

pub mod format;
pub mod sink;

#[doc(inline)]
pub use crate::format::{Cursor, Formattable, Formatter};
#[doc(inline)]
pub use crate::sink::{Printable, PrintableKnownLen, Sink, Indent, Newline};
