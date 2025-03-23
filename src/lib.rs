//! A library for code formatting designed for ease of use.
//!
//! The [`Format`] trait defines how a struct is formatted, and recieves custom `Args`
//! parameter that allows the user to pass around custom state, such as formatting preferences.
//!
//! A [`Format`] implementation requires an associated `Mode` type.
//! The `Mode` type should define all the possible ways that a [`Format`]able type can be formatted,
//! (usually an `enum`). When formatting, `Mode` types are picked by the [`Format::pick_mode`] function,
//! which picks the appropriate mode for the given state.
//!
//! The [`Sink`] trait typically wraps a buffer, and provides facilities for writing text into that buffer.
//! Using a [`Sink`] is similar to using [`fmt::Write`][std::fmt::Write], but some behavior is different:
//! - When the tab (`\t`) character is written, the configured [`Indent`] described by the current [`Cursor`] is written instead.
//! - When the newline (`\n`) character is written, the configured [`Newline`] described by the current [`Cursor`] is written instead,
//!   and the appropriate number of [`Indent`]s are added to return to the current indent level.

#![warn(
  future_incompatible,
  missing_copy_implementations,
  missing_debug_implementations,
  missing_docs,
  unreachable_pub
)]

use std::fmt;

use crate::sealed::Sealed;

pub(crate) mod sealed {
  pub trait Sealed {}
}



/// Contains the current formatter state and basic settings (indentation type, newline style).
#[non_exhaustive]
#[derive(Debug, Clone, Copy)]
pub struct Cursor {
  /// What should be written when indenting.
  pub indent: Indent,
  /// The current indentation level.
  pub indent_level: usize,
  /// What should be written to the sink whenever a newline is encountered.
  pub newline: Newline,
  /// If this flag is set, an indentation is pending and will be added before anything else is written,
  /// unless a newline is written, because the line would only contain whitespace and be redundant.
  pub pending_indent: bool
}

impl Cursor {
  /// Creates a new [`Cursor`].
  pub const fn new(indent: Indent, newline: Newline) -> Self {
    Cursor { indent, indent_level: 0, newline, pending_indent: true }
  }

  /// Adds or subtracts from the current indent level.
  pub fn add_indent(&mut self, change: isize) {
    self.indent_level = self.indent_level.saturating_add_signed(change);
  }

  /// Adds 1 to the current indent level.
  pub fn increment_indent(&mut self) {
    self.indent_level = self.indent_level.saturating_add(1);
  }

  /// Subtracts 1 from the current indent level.
  pub fn decrement_indent(&mut self) {
    self.indent_level = self.indent_level.saturating_sub(1);
  }
}

/// What should be written when indenting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Indent {
  /// Writes the given [`str`] directly.
  String(&'static str),
  /// Writes the given [`char`] the given number of times.
  Repeat(Repeat<char>)
}

impl Indent {
  /// The tab character (`'\t'`).
  pub const TABS: Self = Indent::String("\t");
  /// Two spaces per indent.
  pub const SPACES2: Self = Indent::spaces(2);
  /// Four spaces per indent.
  pub const SPACES4: Self = Indent::spaces(4);
  /// Eight spaces per indent.
  pub const SPACES8: Self = Indent::spaces(8);

  /// Create an `Indent` with an arbitrary number of spaces.
  pub const fn spaces(num: usize) -> Self {
    Indent::Repeat(Repeat::new(' ', num))
  }

  /// The byte length of this indent.
  pub const fn len(self) -> usize {
    match self {
      Self::String(s) => s.len(),
      Self::Repeat(r) => r.len()
    }
  }
}

impl Primitive for Indent {
  #[inline]
  fn len(self) -> usize {
    self.len()
  }

  fn to_buf(self, buf: &mut String) {
    match self {
      Self::String(s) => buf.push_str(s),
      Self::Repeat(r) => r.to_buf(buf)
    };
  }
}

impl fmt::Display for Indent {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match *self {
      Self::String(s) => fmt::Write::write_str(f, s),
      Self::Repeat(r) => fmt::Display::fmt(&r, f)
    }
  }
}

/// What should be written to the sink whenever a newline is encountered.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum Newline {
  /// `"\n"`
  #[default]
  LF,
  /// `"\r\n"`
  CRLF
}

impl Newline {
  /// Converts the [`Newline`] to a `&'static str`.
  pub const fn to_str(self) -> &'static str {
    match self {
      Self::LF => "\n",
      Self::CRLF => "\r\n"
    }
  }
}

impl Primitive for Newline {
  fn len(self) -> usize {
    self.to_str().len()
  }

  fn to_buf(self, buf: &mut String) {
    buf.push_str(self.to_str());
  }
}

impl fmt::Display for Newline {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.write_str(self.to_str())
  }
}



/// Describes how a type can be formatted as text.
pub trait Format<State: Clone>: Sized {
  /// The set of modes by which a [`Format`]able type can be formatted.
  type Mode;

  /// Writes the given value into the sink with the given layout mode.
  fn format(&self, sink: &mut impl Sink, mode: Self::Mode, state: State);

  /// Writes the given value into a string buffer with the given layout mode.
  fn format_to_buf(&self, cursor: Cursor, mode: Self::Mode, state: State) -> String {
    let mut sink = GenericSink::<BufferPlumbing>::new(cursor);
    self.format(&mut sink, mode, state);
    sink.into_buf()
  }

  /// Produces a 'preview' of how the given value will be formatted with the given layout mode.
  ///
  /// This is useful for estimating the final length of a line for a layout mode.
  fn format_to_preview(&self, cursor: Cursor, mode: Self::Mode, state: State) -> Preview {
    let mut sink = GenericSink::<PreviewPlumbing>::new(cursor);
    self.format(&mut sink, mode, state);
    sink.into_preview()
  }

  /// Writes the given value into the sink, picking layout modes automatically.
  ///
  /// This function is equivalent to `self.format(sink, self.pick_mode(sink.cursor(), state.clone()), state)`.
  fn format_auto(&self, sink: &mut impl Sink, state: State) {
    self.format(sink, self.pick_mode(sink.cursor(), state.clone()), state);
  }

  /// Writes the given value into a string buffer, picking layout modes automatically.
  fn format_to_buf_auto(&self, cursor: Cursor, state: State) -> String {
    self.format_to_buf(cursor, self.pick_mode(cursor, state.clone()), state)
  }

  /// Produces a 'preview' of how the given value will be formatted.
  fn format_to_preview_auto(&self, cursor: Cursor, state: State) -> Preview {
    self.format_to_preview(cursor, self.pick_mode(cursor, state.clone()), state)
  }

  /// Picks an appropriate mode to format the current item as, given the current state.
  fn pick_mode(&self, cursor: Cursor, state: State) -> Self::Mode;
}



#[derive(Debug, Clone)]
struct GenericSink<P: Plumbing> {
  plumbing: P,
  cursor: Cursor
}

impl<P: Plumbing> GenericSink<P> {
  fn new(cursor: Cursor) -> Self where P: Default {
    GenericSink { plumbing: P::default(), cursor }
  }
}

impl GenericSink<BufferPlumbing> {
  fn into_buf(self) -> String {
    self.plumbing.buf
  }
}

impl GenericSink<PreviewPlumbing> {
  fn into_preview(self) -> Preview {
    self.plumbing.into_preview()
  }
}

impl<P: Plumbing> Sink for GenericSink<P> {
  fn cursor(&self) -> Cursor {
    self.cursor
  }

  fn cursor_mut(&mut self) -> &mut Cursor {
    &mut self.cursor
  }

  fn write_char(&mut self, c: char) {
    self.plumbing.take_char(&mut self.cursor, c);
  }

  fn write_char_raw(&mut self, c: char) {
    self.plumbing.take_basic(c);
  }

  fn write_str_raw(&mut self, s: &str) {
    self.plumbing.take_basic(s);
  }
}

impl<P: Plumbing> Sealed for GenericSink<P> {}

/// The [`Sink`] trait is similar to using [`fmt::Write`][std::fmt::Write], but some behavior is different:
/// - When the tab (`\t`) character is written, the configured [`Indent`] described by the current [`Cursor`] is written instead.
/// - When the newline (`\n`) character is written, the configured [`Newline`] described by the current [`Cursor`] is written instead,
///   and the appropriate number of [`Indent`]s are added to return to the current indent level.
///
/// [`Sink`] is intentionally not a sub-trait of [`fmt::Write`][std::fmt::Write] in order to indicate that
/// it performs input transformation by default, which may mess with things that use [`fmt::Write`][std::fmt::Write].
///
/// If you need to use a [`Sink`] where only a [`fmt::Write`][std::fmt::Write] are accepted anyways, you can call the
/// [`Sink::as_fmt_write`] or [`Sink::as_fmt_write_raw`] functions to get an adapter value that does implement [`fmt::Write`][std::fmt::Write].
pub trait Sink: Sealed {
  /// Gets the current [`Cursor`].
  fn cursor(&self) -> Cursor;

  /// Gets a mutable reference to the current [`Cursor`].
  /// Modifying the state of the cursor is usually not necessary, and can be done through other means.
  fn cursor_mut(&mut self) -> &mut Cursor;

  /// Writes a single [`char`] into the sink.
  fn write_char(&mut self, c: char);

  /// Writes an entire iterator of [`char`]s into the sink.
  fn write_chars(&mut self, chars: impl IntoIterator<Item = char>) {
    for c in chars {
      self.write_char(c);
    };
  }

  /// Writes an entire [`&str`][str] into the sink.
  fn write_str(&mut self, s: &str) {
    self.write_chars(s.chars());
  }

  /// Functions similarly to [`fmt::Write::write_fmt()`][std::fmt::Write::write_fmt].
  #[inline]
  fn write_fmt(&mut self, args: fmt::Arguments<'_>) {
    fmt::Write::write_fmt(self.as_fmt_write(), args).unwrap()
  }

  /// Writes a single [`char`] directly into the sink, without input transformation.
  fn write_char_raw(&mut self, c: char);

  /// Writes an entire iterator of [`char`]s directly into the sink, without input transformation.
  fn write_chars_raw(&mut self, chars: impl IntoIterator<Item = char>) {
    for c in chars {
      self.write_char_raw(c);
    };
  }

  /// Writes an entire [`&str`][str] directly into the sink, without input transformation.
  fn write_str_raw(&mut self, s: &str) {
    self.write_chars_raw(s.chars());
  }

  /// Functions similarly to [`fmt::Write::write_fmt()`][std::fmt::Write::write_fmt] without input transformation.
  #[inline]
  fn write_fmt_raw(&mut self, args: fmt::Arguments<'_>) {
    fmt::Write::write_fmt(self.as_fmt_write_raw(), args).unwrap()
  }

  /// Convenience function that increments the indent counter before executing the given function, and decrements it afterwards.
  fn indent(&mut self, f: impl FnOnce(&mut Self)) {
    self.cursor_mut().increment_indent();
    f(self);
    self.cursor_mut().decrement_indent();
  }

  /// Returns a handle implementing [`fmt::Write`][std::fmt::Write], with input transformation.
  #[inline]
  fn as_fmt_write(&mut self) -> &mut crate::shim::SinkWrite<Self> {
    crate::shim::SinkWrite::wrap(self)
  }

  /// Returns a handle implementing [`fmt::Write`][std::fmt::Write], without input transformation.
  #[inline]
  fn as_fmt_write_raw(&mut self) -> &mut crate::shim::SinkWriteRaw<Self> {
    crate::shim::SinkWriteRaw::wrap(self)
  }
}



mod shim {
  use super::Sink;

  use std::fmt;

  // The whole point of these shims is to get `std`'s default implementation of `write_fmt()`
  // to call custom implementations of `write_str()` and `write_char()` on `Sink` without
  // implementing `fmt::Write` on `Sink` (because `Sink` behaves a bit differently)
  // and without directly copying `std`'s implementation of `write_fmt()` here.

  #[derive(Debug)]
  #[repr(transparent)]
  pub struct SinkWrite<S: ?Sized>(S);

  impl<S: Sink + ?Sized> SinkWrite<S> {
    #[inline]
    pub(crate) fn wrap(sink: &mut S) -> &mut Self {
      // SAFETY: `SinkWrite` is repr(transparent) and thus has the same repr as `S`
      unsafe { &mut *(sink as *mut S as *mut Self) }
    }
  }

  impl<S: Sink + ?Sized> fmt::Write for SinkWrite<S> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
      self.0.write_str(s);
      Ok(())
    }

    #[inline]
    fn write_char(&mut self, c: char) -> fmt::Result {
      self.0.write_char(c);
      Ok(())
    }
  }

  #[derive(Debug)]
  #[repr(transparent)]
  pub struct SinkWriteRaw<S: ?Sized>(S);

  impl<S: Sink + ?Sized> SinkWriteRaw<S> {
    #[inline]
    pub(crate) fn wrap(sink: &mut S) -> &mut Self {
      // SAFETY: `SinkWriteRaw` is repr(transparent) and thus has the same repr as `S`
      unsafe { &mut *(sink as *mut S as *mut Self) }
    }
  }

  impl<S: Sink + ?Sized> fmt::Write for SinkWriteRaw<S> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
      self.0.write_str_raw(s);
      Ok(())
    }

    #[inline]
    fn write_char(&mut self, c: char) -> fmt::Result {
      self.0.write_char_raw(c);
      Ok(())
    }
  }
}



#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct BufferPlumbing {
  buf: String
}

impl Plumbing for BufferPlumbing {
  fn take_basic(&mut self, primitive: impl Primitive) {
    primitive.to_buf(&mut self.buf);
  }

  #[inline]
  fn take_newline(&mut self, primitive: impl Primitive) {
    self.take_basic(primitive);
  }
}

impl Sealed for BufferPlumbing {}

/// The [`Preview`] struct gives you a basic overview of how something will be formatted, at a lower cost.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Preview {
  /// The total length (in bytes) of the output.
  pub len: usize,
  /// The number of rows spanned by the output.
  pub vertical_span: usize,
  /// The number of columns spanned by the output, i.e. the length of the longest row.
  pub horizontal_span: usize
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PreviewPlumbing {
  len: usize,
  vertical_span: usize,
  horizontal_span: usize,
  current_column: usize
}

impl PreviewPlumbing {
  fn into_preview(self) -> Preview {
    let horizontal_span = usize::max(self.horizontal_span, self.current_column);
    Preview { len: self.len, vertical_span: self.vertical_span, horizontal_span }
  }
}

impl Default for PreviewPlumbing {
  fn default() -> Self {
    PreviewPlumbing {
      len: 0,
      vertical_span: 1,
      horizontal_span: 0,
      current_column: 0
    }
  }
}

impl Plumbing for PreviewPlumbing {
  fn take_basic(&mut self, primitive: impl Primitive) {
    let len = primitive.len();
    self.len += len;
    self.current_column += len;
  }

  fn take_newline(&mut self, primitive: impl Primitive) {
    let column = std::mem::take(&mut self.current_column);
    self.len += primitive.len();
    self.vertical_span += 1;
    self.horizontal_span = usize::max(self.horizontal_span, column);
    self.current_column = 0;
  }
}

impl Sealed for PreviewPlumbing {}

trait Plumbing: Sealed {
  fn take_basic(&mut self, primitive: impl Primitive);
  fn take_newline(&mut self, primitive: impl Primitive);

  /// Indents at the start of lines are not written until just before something else is written.
  /// This forces a pending indent to be written out, and should be called before writing anything else.
  fn take_pending_indent(&mut self, cursor: &mut Cursor) {
    if std::mem::take(&mut cursor.pending_indent) {
      self.take_basic(Repeat::new(cursor.indent, cursor.indent_level));
    };
  }

  fn take_char(&mut self, cursor: &mut Cursor, c: char) {
    match c {
      '\n' => {
        self.take_newline(cursor.newline);
        cursor.pending_indent = true;
      },
      '\t' => {
        self.take_pending_indent(cursor);
        self.take_basic(cursor.indent);
      },
      c => {
        self.take_pending_indent(cursor);
        self.take_basic(c);
      }
    };
  }
}



/// A [`Primitive`] is a type that has a fixed (or easily calculable) length, and can be written into a [`String`].
trait Primitive {
  fn len(self) -> usize;
  fn to_buf(self, buf: &mut String);
}

impl Primitive for char {
  fn len(self) -> usize {
    self.len_utf8()
  }

  fn to_buf(self, buf: &mut String) {
    buf.push(self);
  }
}

impl Primitive for &str {
  fn len(self) -> usize {
    self.len()
  }

  fn to_buf(self, buf: &mut String) {
    buf.push_str(self)
  }
}

/// Repeats the given value N times.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Repeat<P> {
  /// The value to repeat.
  pub value: P,
  /// The number of times to repeat.
  pub count: usize
}

impl<P> Repeat<P> {
  /// Creates a new [`Repeat`].
  #[inline]
  pub const fn new(value: P, count: usize) -> Self {
    Repeat { value, count }
  }
}

impl Repeat<char> {
  /// Returns `true` if `len` would return `0`.
  #[inline]
  pub const fn is_empty(self) -> bool {
    // `len_utf8` is always "between 1 and 4, inclusive",
    // therefore `len` will never return 0
    false
  }

  /// The length of the value when stringified.
  pub const fn len(self) -> usize {
    self.value.len_utf8() * self.count
  }
}

impl Repeat<&str> {
  /// Returns `true` if `len` would return `0`.
  #[inline]
  pub const fn is_empty(self) -> bool {
    self.value.is_empty()
  }

  /// The length of the value when stringified.
  pub const fn len(self) -> usize {
    self.value.len() * self.count
  }
}

impl<P: Primitive + Clone> Primitive for Repeat<P> {
  fn len(self) -> usize {
    self.value.len() * self.count
  }

  fn to_buf(self, buf: &mut String) {
    buf.reserve(self.clone().len());
    for _ in 0..self.count {
      self.value.clone().to_buf(buf);
    };
  }
}

impl<P: fmt::Display> fmt::Display for Repeat<P> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for _ in 0..self.count {
      fmt::Display::fmt(&self.value, f)?;
    };

    Ok(())
  }
}
