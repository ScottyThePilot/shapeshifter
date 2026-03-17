//! Internals relating to [`Sink`] and [`Printable`].

#[cfg(feature = "printable_numbers")]
mod numbers;

use bytemuck::TransparentWrapper;

use std::fmt;



/// A value which may be written into a [`Sink`].
pub trait Printable {
  /// Writes the value into the given [`Sink`].
  fn print(&self, sink: &mut (impl Sink + ?Sized));
}

impl Printable for char {
  fn print(&self, sink: &mut (impl Sink + ?Sized)) {
    sink.write_char(*self);
  }
}

impl Printable for str {
  fn print(&self, sink: &mut (impl Sink + ?Sized)) {
    sink.write_str(self);
  }
}

impl<T> Printable for [T] where T: Printable {
  fn print(&self, sink: &mut (impl Sink + ?Sized)) {
    self.iter().for_each(|printable| printable.print(sink));
  }
}



/// A value who's textual representation is of a known length.
///
/// This should be consistent with the type's [`Printable`] implementation.
pub trait PrintableKnownLen: Printable {
  /// Returns the length of the value's textual representation.
  fn print_len(&self) -> usize;
}

impl PrintableKnownLen for char {
  fn print_len(&self) -> usize {
    self.len_utf8()
  }
}

impl PrintableKnownLen for str {
  fn print_len(&self) -> usize {
    self.len()
  }
}

impl<T> PrintableKnownLen for [T] where T: PrintableKnownLen {
  fn print_len(&self) -> usize {
    self.iter().map(T::print_len).sum()
  }
}



macro_rules! impl_printable_delegate {
  ($T:ident for $Type:ty) => (
    impl<$T: $crate::sink::Printable + ?Sized> $crate::sink::Printable for $Type {
      #[inline]
      fn print(&self, sink: &mut (impl $crate::sink::Sink + ?Sized)) {
        $T::print(self, sink)
      }
    }

    impl<$T: $crate::sink::PrintableKnownLen + ?Sized> $crate::sink::PrintableKnownLen for $Type {
      #[inline]
      fn print_len(&self) -> usize {
        $T::print_len(self)
      }
    }
  );
}

impl_printable_delegate!(T for &T);
impl_printable_delegate!(T for &mut T);
impl_printable_delegate!(T for Box<T>);
impl_printable_delegate!(T for std::rc::Rc<T>);
impl_printable_delegate!(T for std::sync::Arc<T>);



/// Implements [`Printable`] and [`PrintableKnownLen`]
/// for the given type, based on that type's [`AsRef<str>`][AsRef] implementation.
#[macro_export]
macro_rules! impl_printable_from_asref_str {
  ($Type:ty) => (
    impl $crate::sink::Printable for $Type {
      #[inline]
      fn print(&self, sink: &mut (impl $crate::sink::Sink + ?Sized)) {
        $crate::sink::Sink::write_str(sink, AsRef::as_ref(self))
      }
    }

    impl $crate::sink::PrintableKnownLen for $Type {
      #[inline]
      fn print_len(&self) -> usize {
        str::len(AsRef::as_ref(self))
      }
    }
  );
}

/// Implements [`Printable`] and [`PrintableKnownLen`]
/// for the given type, based on that type's [`fmt::Debug`][std::fmt::Debug] implementation.
#[macro_export]
macro_rules! impl_printable_from_debug {
  ($Type:ty) => (
    impl $crate::sink::Printable for $Type {
      #[inline]
      fn print(&self, sink: &mut (impl $crate::sink::Sink + ?Sized)) {
        $crate::sink::Sink::write_fmt(sink, format_args!("{self:?}"))
      }
    }

    impl $crate::sink::PrintableKnownLen for $Type {
      #[inline]
      fn print_len(&self) -> usize {
        $crate::sink::fmt_debug_len(self)
      }
    }
  );
}

/// Implements [`Printable`] and [`PrintableKnownLen`]
/// for the given type, based on that type's [`fmt::Display`][std::fmt::Display] implementation.
#[macro_export]
macro_rules! impl_printable_from_display {
  ($Type:ty) => (
    impl $crate::sink::Printable for $Type {
      #[inline]
      fn print(&self, sink: &mut (impl $crate::sink::Sink + ?Sized)) {
        $crate::sink::Sink::write_fmt(sink, format_args!("{self}"))
      }
    }

    impl $crate::sink::PrintableKnownLen for $Type {
      #[inline]
      fn print_len(&self) -> usize {
        $crate::sink::fmt_display_len(self)
      }
    }
  );
}

/// Implements [`PrintableKnownLen`] for the given type, based on that type's [`Printable`] implementation
/// by measuring the output length of the printed value.
///
/// This should only be used as a fallback in cases when the length of a [`Printable`] value cannot be easily determined.
#[macro_export]
macro_rules! impl_printable_known_length_fallback {
  ($Type:ty) => (
    impl $crate::sink::PrintableKnownLen for $Type {
      #[inline]
      fn print_len(&self) -> usize {
        $crate::sink::printable_len(self)
      }
    }
  );
}



/// A generic output text stream, akin to [`fmt::Write`], but specialized for the purposes of this library.
pub trait Sink {
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

  /// Functions similarly to [`fmt::Write::write_fmt()`][fmt::Write::write_fmt].
  #[inline]
  fn write_fmt(&mut self, args: fmt::Arguments<'_>) {
    fmt::Write::write_fmt(self.as_fmt_write(), args).unwrap()
  }

  /// Returns a handle implementing [`fmt::Write`].
  #[inline]
  fn as_fmt_write(&mut self) -> &mut SinkWrite<Self> {
    SinkWrite::wrap_mut(self)
  }
}

impl Sink for String {
  fn write_char(&mut self, c: char) {
    self.push(c);
  }

  fn write_chars(&mut self, chars: impl IntoIterator<Item = char>) {
    self.extend(chars);
  }

  fn write_str(&mut self, s: &str) {
    self.push_str(s);
  }
}

macro_rules! impl_sink_delegate {
  ($T:ident for $Type:ty) => (
    impl<$T: $crate::sink::Sink + ?Sized> $crate::sink::Sink for $Type {
      #[inline]
      fn write_char(&mut self, c: char) {
        $T::write_char(self, c)
      }

      #[inline]
      fn write_chars(&mut self, chars: impl IntoIterator<Item = char>) {
        $T::write_chars(self, chars)
      }

      #[inline]
      fn write_str(&mut self, s: &str) {
        $T::write_str(self, s)
      }
    }
  );
}

impl_sink_delegate!(T for &mut T);
impl_sink_delegate!(T for Box<T>);



/// A wrapper type that allows a [`Sink`] to be used like a [`fmt::Write`].
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct SinkWrite<S: ?Sized>(S);

unsafe impl<S: ?Sized> TransparentWrapper<S> for SinkWrite<S> {}

impl<S: Sink + ?Sized> fmt::Write for SinkWrite<S> {
  fn write_str(&mut self, s: &str) -> fmt::Result {
    self.0.write_str(s);
    Ok(())
  }

  fn write_char(&mut self, c: char) -> fmt::Result {
    self.0.write_char(c);
    Ok(())
  }
}

/// A wrapper type that allows a [`fmt::Write`] to be used like a [`Sink`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct WriteSink<W> {
  writer: W,
  err: Option<fmt::Error>
}

impl<W: fmt::Write> WriteSink<W> {
  /// Create a new [`WriteSink`] from a [`fmt::Write`].
  pub const fn new(writer: W) -> Self {
    WriteSink { writer, err: None }
  }

  /// If an error was encountered when writing to the internal [`fmt::Write`], this will retrieve it.
  pub const fn take_err(&mut self) -> Option<fmt::Error> {
    self.err.take()
  }
}

impl<W: fmt::Write> Sink for WriteSink<W> {
  fn write_char(&mut self, c: char) {
    if let Err(err) = self.writer.write_char(c) {
      self.err.replace(err);
    };
  }

  fn write_str(&mut self, s: &str) {
    if let Err(err) = self.writer.write_str(s) {
      self.err.replace(err);
    };
  }

  fn write_fmt(&mut self, args: fmt::Arguments<'_>) {
    if let Err(err) = self.writer.write_fmt(args) {
      self.err.replace(err);
    };
  }
}

/// Writes a [`Printable`] into a [`fmt::Write`].
pub fn fmt_write_printable<W, T>(writer: &mut W, printable: &T) -> fmt::Result
where W: fmt::Write + ?Sized, T: Printable + ?Sized {
  fmt_write_as_sink(writer, |sink| printable.print(sink))
}

/// Allows a [`fmt::Write`] to be used like a [`Sink`].
pub fn fmt_write_as_sink<W, F>(writer: &mut W, f: F) -> fmt::Result
where W: fmt::Write + ?Sized, F: FnOnce(&mut WriteSink<&mut W>) {
  let mut sink = WriteSink::new(writer);
  f(&mut sink);
  match sink.take_err() {
    Some(err) => Err(err),
    None => Ok(())
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

impl Printable for Indent {
  fn print(&self, sink: &mut (impl Sink + ?Sized)) {
    match self {
      Self::String(s) => s.print(sink),
      Self::Repeat(r) => r.print(sink)
    };
  }
}

impl PrintableKnownLen for Indent {
  fn print_len(&self) -> usize {
    match self {
      Self::String(s) => s.print_len(),
      Self::Repeat(r) => r.print_len()
    }
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

impl AsRef<str> for Newline {
  #[inline]
  fn as_ref(&self) -> &str {
    self.to_str()
  }
}

impl_printable_from_asref_str!(Newline);

impl fmt::Display for Newline {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.write_str(self.to_str())
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
  pub const fn new(value: P, count: usize) -> Self {
    Repeat { value, count }
  }
}

impl Repeat<char> {
  /// The length of the value when stringified.
  pub const fn len(self) -> usize {
    self.value.len_utf8() * self.count
  }
}

impl Repeat<&str> {
  /// The length of the value when stringified.
  pub const fn len(self) -> usize {
    self.value.len() * self.count
  }
}

impl<P: Printable> Printable for Repeat<P> {
  fn print(&self, sink: &mut (impl Sink + ?Sized)) {
    for _ in 0..self.count {
      self.value.print(sink);
    };
  }
}

impl<P: PrintableKnownLen> PrintableKnownLen for Repeat<P> {
  fn print_len(&self) -> usize {
    self.value.print_len() * self.count
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



/// Measures the length of `T` when formatted with its [`Printable`] implementation.
///
/// This function should be used sparingly, and only in implementations of [`PrintableKnownLen`]
/// where the length of a [`Printable`] value cannot be easily determined.
pub fn printable_len<T: Printable + ?Sized>(value: &T) -> usize {
  let mut counter = Counter(0);
  value.print(&mut counter);
  counter.0
}

/// Measures the length of `T` when formatted with its [`fmt::Debug`] implementation.
pub fn fmt_debug_len<T: fmt::Debug + ?Sized>(value: &T) -> usize {
  fmt_args_len(format_args!("{value:?}"))
}

/// Measures the length of `T` when formatted with its [`fmt::Display`] implementation.
pub fn fmt_display_len<T: fmt::Display + ?Sized>(value: &T) -> usize {
  fmt_args_len(format_args!("{value}"))
}

/// Measures the length of a [`fmt::Arguments`] when formatted.
pub fn fmt_args_len(args: fmt::Arguments<'_>) -> usize {
  let mut counter = Counter(0);
  fmt::Write::write_fmt(&mut counter, args).unwrap();
  counter.0
}



#[derive(Debug)]
struct Counter(usize);

impl Sink for Counter {
  fn write_char(&mut self, c: char) {
    self.0 += c.len_utf8();
  }

  fn write_str(&mut self, s: &str) {
    self.0 += s.len();
  }
}

impl fmt::Write for Counter {
  fn write_char(&mut self, c: char) -> fmt::Result {
    self.0 += c.len_utf8();
    Ok(())
  }

  fn write_str(&mut self, s: &str) -> fmt::Result {
    self.0 += s.len();
    Ok(())
  }
}
