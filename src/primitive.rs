//! Internals relating to [`fmt::Write`], [`fmt::Display`] and [`fmt::Debug`].

use itoa::{Buffer, Integer};

use std::fmt;



/// Extensions to [`fmt::Display`].
pub trait DisplayExt: fmt::Display {
  /// The length of this value, in chars, when printed via [`fmt::Display`].
  fn fmt_chars_len(&self) -> Result<usize, fmt::Error>;

  /// The length of this value, in bytes, when printed via [`fmt::Display`].
  fn fmt_bytes_len(&self) -> Result<usize, fmt::Error>;
}

impl<T> DisplayExt for T where T: fmt::Display + ?Sized {
  fn fmt_chars_len(&self) -> Result<usize, fmt::Error> {
    fmt_display_chars_len(self)
  }

  fn fmt_bytes_len(&self) -> Result<usize, fmt::Error> {
    fmt_display_bytes_len(self)
  }
}

/// Extensions to [`fmt::Debug`].
pub trait DebugExt: fmt::Debug {
  /// The length of this value, in chars, when printed via [`fmt::Debug`].
  fn fmt_chars_len(&self) -> Result<usize, fmt::Error>;

  /// The length of this value, in bytes, when printed via [`fmt::Debug`].
  fn fmt_bytes_len(&self) -> Result<usize, fmt::Error>;
}

impl<T> DebugExt for T where T: fmt::Debug + ?Sized {
  fn fmt_chars_len(&self) -> Result<usize, fmt::Error> {
    fmt_debug_chars_len(self)
  }

  fn fmt_bytes_len(&self) -> Result<usize, fmt::Error> {
    fmt_debug_bytes_len(self)
  }
}

/// Extensions to [`fmt::Write`].
pub trait WriteExt: fmt::Write {
  /// Write a newline `"\n"` into this [`fmt::Write`].
  fn write_nl(&mut self) -> fmt::Result;

  /// Write an integer into this [`fmt::Write`].
  fn write_int(&mut self, int: impl Integer) -> fmt::Result;

  /// Write a value implementing [`fmt::Display`] into this [`fmt::Write`].
  fn write_display<D: fmt::Display + ?Sized>(&mut self, value: &D) -> fmt::Result;

  /// Write a value implementing [`fmt::Debug`] into this [`fmt::Write`].
  fn write_debug<D: fmt::Debug + ?Sized>(&mut self, value: &D) -> fmt::Result;
}

impl<T> WriteExt for T where T: fmt::Write + ?Sized {
  fn write_nl(&mut self) -> fmt::Result {
    self.write_char('\n')
  }

  fn write_int(&mut self, int: impl Integer) -> fmt::Result {
    self.write_str(Buffer::new().format(int))
  }

  fn write_display<D: fmt::Display + ?Sized>(&mut self, value: &D) -> fmt::Result {
    write!(self, "{value}")
  }

  fn write_debug<D: fmt::Debug + ?Sized>(&mut self, value: &D) -> fmt::Result {
    write!(self, "{value:?}")
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

  /// The length of this newline, in chars.
  pub const fn chars_len(self) -> usize {
    match self {
      Self::LF => 1,
      Self::CRLF => 2
    }
  }
}

impl AsRef<str> for Newline {
  #[inline]
  fn as_ref(&self) -> &str {
    self.to_str()
  }
}

impl fmt::Display for Newline {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.write_str(self.to_str())
  }
}

impl IntoIterator for Newline {
  type Item = char;
  type IntoIter = std::str::Chars<'static>;

  fn into_iter(self) -> Self::IntoIter {
    self.to_str().chars()
  }
}



/// What should be written when indenting.
pub type Indent = Repeat<char>;

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
  /// The tab character (`'\t'`).
  pub const TABS: Self = Repeat::new('\t', 1);
  /// Two spaces.
  pub const SPACES2: Self = Repeat::new(' ', 2);
  /// Four spaces.
  pub const SPACES4: Self = Repeat::new(' ', 4);
  /// Eight spaces.
  pub const SPACES8: Self = Repeat::new(' ', 8);

  /// The length of this [`Repeat<char>`], in chars.
  pub const fn chars_len(self) -> usize {
    self.count
  }
}

impl Repeat<Repeat<char>> {
  /// The length of this [`Repeat<Repeat<char>>`], in chars.
  pub const fn chars_len(self) -> usize {
    self.value.count * self.count
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

impl IntoIterator for Repeat<char> {
  type Item = char;
  type IntoIter = std::iter::RepeatN<char>;

  fn into_iter(self) -> Self::IntoIter {
    std::iter::repeat_n(self.value, self.chars_len())
  }
}

impl IntoIterator for Repeat<Repeat<char>> {
  type Item = char;
  type IntoIter = std::iter::RepeatN<char>;

  fn into_iter(self) -> Self::IntoIter {
    std::iter::repeat_n(self.value.value, self.chars_len())
  }
}



#[derive(Debug)]
struct CharsCounter(usize);

impl fmt::Write for CharsCounter {
  fn write_char(&mut self, _: char) -> fmt::Result {
    self.0 += 1;
    Ok(())
  }

  fn write_str(&mut self, s: &str) -> fmt::Result {
    self.0 += s.chars().count();
    Ok(())
  }
}

/// Measures the length of `T`, in chars, when formatted with its [`fmt::Debug`] implementation.
pub fn fmt_debug_chars_len<T: fmt::Debug + ?Sized>(value: &T) -> Result<usize, fmt::Error> {
  fmt_args_chars_len(format_args!("{value:?}"))
}

/// Measures the length of `T`, in chars, when formatted with its [`fmt::Display`] implementation.
pub fn fmt_display_chars_len<T: fmt::Display + ?Sized>(value: &T) -> Result<usize, fmt::Error> {
  fmt_args_chars_len(format_args!("{value}"))
}

/// Measures the length of a [`fmt::Arguments`], in chars, when formatted.
pub fn fmt_args_chars_len(args: fmt::Arguments<'_>) -> Result<usize, fmt::Error> {
  let mut counter = CharsCounter(0);
  fmt::Write::write_fmt(&mut counter, args)?;
  Ok(counter.0)
}



#[derive(Debug)]
struct BytesCounter(usize);

impl fmt::Write for BytesCounter {
  fn write_char(&mut self, c: char) -> fmt::Result {
    self.0 += c.len_utf8();
    Ok(())
  }

  fn write_str(&mut self, s: &str) -> fmt::Result {
    self.0 += s.len();
    Ok(())
  }
}

/// Measures the length of `T`, in bytes, when formatted with its [`fmt::Debug`] implementation.
pub fn fmt_debug_bytes_len<T: fmt::Debug + ?Sized>(value: &T) -> Result<usize, fmt::Error> {
  fmt_args_bytes_len(format_args!("{value:?}"))
}

/// Measures the length of `T`, in bytes, when formatted with its [`fmt::Display`] implementation.
pub fn fmt_display_bytes_len<T: fmt::Display + ?Sized>(value: &T) -> Result<usize, fmt::Error> {
  fmt_args_bytes_len(format_args!("{value}"))
}

/// Measures the length of a [`fmt::Arguments`], in bytes, when formatted.
pub fn fmt_args_bytes_len(args: fmt::Arguments<'_>) -> Result<usize, fmt::Error> {
  let mut counter = BytesCounter(0);
  fmt::Write::write_fmt(&mut counter, args)?;
  Ok(counter.0)
}
