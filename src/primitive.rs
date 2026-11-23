//! Internals relating to [`fmt::Write`], [`fmt::Display`] and [`fmt::Debug`].

use itoa::{Buffer, Integer};

use std::fmt;



/// Extensions to [`fmt::Display`].
pub trait DisplayExt: fmt::Display {
  /// The length of this value, when printed via [`fmt::Display`].
  fn fmt_len(&self) -> Result<usize, fmt::Error>;
}

impl<T> DisplayExt for T where T: fmt::Display + ?Sized {
  fn fmt_len(&self) -> Result<usize, fmt::Error> {
    fmt_display_len(self)
  }
}

/// Extensions to [`fmt::Debug`].
pub trait DebugExt: fmt::Debug {
  /// The length of this value, when printed via [`fmt::Debug`].
  fn fmt_len(&self) -> Result<usize, fmt::Error>;
}

impl<T> DebugExt for T where T: fmt::Debug + ?Sized {
  fn fmt_len(&self) -> Result<usize, fmt::Error> {
    fmt_debug_len(self)
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

impl<P: fmt::Display> fmt::Display for Repeat<P> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for _ in 0..self.count {
      fmt::Display::fmt(&self.value, f)?;
    };

    Ok(())
  }
}



/// Measures the length of `T` when formatted with its [`fmt::Debug`] implementation.
pub fn fmt_debug_len<T: fmt::Debug + ?Sized>(value: &T) -> Result<usize, fmt::Error> {
  fmt_args_len(format_args!("{value:?}"))
}

/// Measures the length of `T` when formatted with its [`fmt::Display`] implementation.
pub fn fmt_display_len<T: fmt::Display + ?Sized>(value: &T) -> Result<usize, fmt::Error> {
  fmt_args_len(format_args!("{value}"))
}

/// Measures the length of a [`fmt::Arguments`] when formatted.
pub fn fmt_args_len(args: fmt::Arguments<'_>) -> Result<usize, fmt::Error> {
  let mut counter = Counter(0);
  fmt::Write::write_fmt(&mut counter, args)?;
  Ok(counter.0)
}



#[derive(Debug)]
struct Counter(usize);

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
