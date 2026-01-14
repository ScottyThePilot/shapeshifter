//! Utilities for streamlining certain common practices.

use crate::{Cursor, Format, Sink, SinkDisplay};

use std::ops::Deref;



/// Helpers for instantiating structs like [`FormatDelimited`] and [`FormatSeparated`] easily.
pub trait Helpers: Sized {
  /// Creates a new [`FormatDelimited`].
  fn delimited<D>(self, delimiter_start: D, delimiter_end: D) -> FormatDelimited<D, Self>
  where D: SinkDisplay;

  /// Creates a new [`FormatSeparated`].
  fn separated<S>(self, separator: S, trailing: bool) -> FormatSeparated<S, Self>
  where S: SinkDisplay, Self: Deref, for<'t> &'t Self::Target: IntoIterator;

  /// Creates a new [`FormatIndented`].
  fn indented(self) -> FormatIndented<Self>;
}

impl<T> Helpers for T where T: Sized {
  fn delimited<D>(self, delimiter_start: D, delimiter_end: D) -> FormatDelimited<D, Self> {
    FormatDelimited::new(delimiter_start, delimiter_end, self)
  }

  fn separated<S>(self, separator: S, trailing: bool) -> FormatSeparated<S, Self> {
    FormatSeparated::new(separator, trailing, self)
  }

  fn indented(self) -> FormatIndented<Self> {
    FormatIndented::new(self)
  }
}



/// A basic formatter implementation that formats a value, indented by one tab.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FormatIndented<T> {
  inner: T
}

impl<T> FormatIndented<T> {
  /// Creates a new [`FormatIndented`].
  pub const fn new(inner: T) -> Self {
    FormatIndented { inner }
  }
}

impl<T, State: Clone> Format<State> for FormatIndented<T>
where T: Format<State> {
  type Mode = ();

  fn format(&self, sink: &mut impl Sink, (): Self::Mode, state: State) {
    sink.indent(|sink| self.inner.format_auto(sink, state));
  }

  fn pick_mode(&self, _: Cursor, _: State) -> Self::Mode {
    ()
  }
}



/// A basic formatter implementation that formats a value, delimited by two given delmiter strings on either side.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FormatDelimited<D, T> {
  delimiter_start: D,
  delimiter_end: D,
  inner: T
}

impl<D, T> FormatDelimited<D, T> {
  /// Creates a new [`FormatDelimited`].
  #[inline]
  pub const fn new(delimiter_start: D, delimiter_end: D, inner: T) -> Self {
    FormatDelimited { delimiter_start, delimiter_end, inner }
  }
}

impl<D, T, State: Clone> Format<State> for FormatDelimited<D, T>
where D: SinkDisplay, T: Format<State> {
  type Mode = ();

  fn format(&self, sink: &mut impl Sink, (): Self::Mode, state: State) {
    sink.display(self.delimiter_start);
    self.inner.format_auto(sink, state);
    sink.display(self.delimiter_end);
  }

  fn pick_mode(&self, _: Cursor, _: State) -> Self::Mode {
    ()
  }
}



/// A basic formatter implementation that formats a list of values, separated by a given separator string.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FormatSeparated<S, T> {
  separator: S,
  trailing: bool,
  inner: T
}

impl<S, T> FormatSeparated<S, T> {
  /// Creates a new [`FormatSeparated`].
  #[inline]
  pub const fn new(separator: S, trailing: bool, inner: T) -> Self {
    FormatSeparated { separator, trailing, inner }
  }
}

impl<S, T, State: Clone> Format<State> for FormatSeparated<S, T>
where S: SinkDisplay, T: Deref, for<'t> &'t T::Target: IntoIterator<Item: Format<State>> {
  type Mode = ();

  fn format(&self, sink: &mut impl Sink, (): Self::Mode, state: State) {
    for (i, value) in self.inner.into_iter().enumerate() {
      if i != 0 { sink.display(self.separator); };
      value.format_auto(sink, state.clone());
    };

    if self.trailing {
      sink.display(self.separator);
    };
  }

  fn pick_mode(&self, _: Cursor, _: State) -> Self::Mode {
    ()
  }
}
