//! Internals relating to [`Formattable`] and [`Formatter`].

use crate::sink::{
  Printable,
  PrintableKnownLen,
  Indent,
  Newline,
  Repeat,
  Sink
};

use bytemuck::TransparentWrapper;



/// Contains the current formatter state and basic settings (indentation type, newline style).
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
  /// Tab character (`'\t'`) as indent, with Unix-style line endings.
  pub const DEFAULT_UNIX_TABS: Self = Cursor::new(Indent::TABS, Newline::LF);
  /// Tab character (`'\t'`) as indent, with Windows-style line endings.
  pub const DEFAULT_WIN_TABS: Self = Cursor::new(Indent::TABS, Newline::CRLF);
  /// Two spaces per indent, with Unix-style line endings.
  pub const DEFAULT_UNIX_SPACES2: Self = Cursor::new(Indent::SPACES2, Newline::LF);
  /// Two spaces per indent, with Windows-style line endings.
  pub const DEFAULT_WIN_SPACES2: Self = Cursor::new(Indent::SPACES2, Newline::CRLF);
  /// Four spaces per indent, with Unix-style line endings.
  pub const DEFAULT_UNIX_SPACES4: Self = Cursor::new(Indent::SPACES4, Newline::LF);
  /// Four spaces per indent, with Windows-style line endings.
  pub const DEFAULT_WIN_SPACES4: Self = Cursor::new(Indent::SPACES4, Newline::CRLF);
  /// Eight spaces per indent, with Unix-style line endings.
  pub const DEFAULT_UNIX_SPACES8: Self = Cursor::new(Indent::SPACES8, Newline::LF);
  /// Eight spaces per indent, with Windows-style line endings.
  pub const DEFAULT_WIN_SPACES8: Self = Cursor::new(Indent::SPACES8, Newline::CRLF);

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



/// Describes how a type can be adaptively formatted as text.
///
/// The [`Formattable`] trait takes a custom `State` parameter that allows
/// the user to pass around custom state, such as formatting preferences.
///
/// A [`Formattable`] implementation requires an associated `Layout` type, which encodes the totality of
/// ways in which the value may be formatted. When formatting automatically (via [`format_auto`][Formattable::format_auto]
/// or otherwise), it will pick a layout mode itself with the [`pick_layout`][Formattable::pick_layout] method,
/// which specifies what layout mode should be used for the given item in the given scenario.
///
/// Most methods on [`Formattable`] pass in a [`Formatter`] which is akin to [`fmt::Formatter`][std::fmt::Formatter],
/// but implements [`Sink`] rather than [`fmt::Write`][std::fmt::Write] (see [`Sink`] for more information).
///
/// ## Usage
/// - If you are implementing this trait yourself, you only need to implement the
///   [`format`][Formattable::format] and [`pick_layout`][Formattable::pick_layout] methods.
/// - If you are trying to format a value within a [`Formattable`] implementation, you likely want to use
///   [`format`][Formattable::format] or [`format_auto`][Formattable::format_auto] depending on whether the formatter
///   should pick a layout for you, or you would like to specify one yourself.
/// - If you are trying to produce a preview for use inside [`pick_layout`][Formattable::pick_layout], only
///   use [`format_to_preview`][Formattable::format_to_preview], as [`format_to_preview_auto`][Formattable::format_to_preview_auto]
///   calls [`pick_layout`][Formattable::pick_layout] itself to determine the layout mode and will cause an infinite loop.
/// - If you are trying to produce a final output string for your type, use [`format_to_string_auto`][Formattable::format_to_string_auto].
pub trait Formattable<State: Clone>: Sized {
  /// The set of layout modes by which a [`Formattable`] type can be formatted.
  type Layout;

  /// Picks an appropriate layout mode to format the current item with, given the current state.
  fn pick_layout(&self, cursor: Cursor, state: State) -> Self::Layout;

  /// Writes the given value into the sink with the given layout mode.
  fn format(&self, formatter: &mut (impl Formatter + ?Sized), layout: Self::Layout, state: State);

  /// Performs a formatting job, producing its output, given a [`Plumbing`].
  fn format_to<P>(&self, cursor: Cursor, layout: Self::Layout, state: State) -> P::Output
  where P: Plumbing + Default {
    let mut formatter = GenericFormatter::<P>::new(cursor);
    self.format(&mut formatter, layout, state);
    formatter.into_output()
  }

  /// Writes the given value into a string buffer with the given layout mode.
  ///
  /// This function is equivalent to `self.format_to::<StringPlumbing>(cursor, layout, state)`.
  #[inline]
  fn format_to_string(&self, cursor: Cursor, layout: Self::Layout, state: State) -> String {
    self.format_to::<StringPlumbing>(cursor, layout, state)
  }

  /// Produces a 'preview' of how the given value will be formatted with the given layout mode.
  ///
  /// This is useful for estimating the final length of a line for a layout mode.
  ///
  /// This function is equivalent to `self.format_to::<PreviewPlumbing>(cursor, layout, state)`.
  #[inline]
  fn format_to_preview(&self, cursor: Cursor, layout: Self::Layout, state: State) -> Preview {
    self.format_to::<PreviewPlumbing>(cursor, layout, state)
  }

  /// Writes the given value into the formatter, picking layout modes automatically.
  ///
  /// This function is equivalent to `self.format(formatter, self.pick_layout(formatter.cursor(), state.clone()), state)`.
  #[inline]
  fn format_auto(&self, formatter: &mut (impl Formatter + ?Sized), state: State) {
    self.format(formatter, self.pick_layout(formatter.cursor(), state.clone()), state);
  }

  /// Performs a formatting job, producing its output, given a [`Plumbing`], picking layout modes automatically.
  ///
  /// This function is equivalent to `self.format_to::<P>(cursor, self.pick_layout(cursor, state.clone()), state)`.
  #[inline]
  fn format_to_auto<P>(&self, cursor: Cursor, state: State) -> P::Output
  where P: Plumbing + Default {
    self.format_to::<P>(cursor, self.pick_layout(cursor, state.clone()), state)
  }

  /// Writes the given value into a string buffer, picking layout modes automatically.
  ///
  /// This function is equivalent to `self.format_to_auto::<StringPlumbing>(cursor, state)`.
  #[inline]
  fn format_to_string_auto(&self, cursor: Cursor, state: State) -> String {
    self.format_to_auto::<StringPlumbing>(cursor, state)
  }

  /// Produces a 'preview' of how the given value will be formatted, picking layout modes automatically.
  ///
  /// This function is equivalent to `self.format_to_auto::<PreviewPlumbing>(cursor, state)`.
  #[inline]
  fn format_to_preview_auto(&self, cursor: Cursor, state: State) -> Preview {
    self.format_to_auto::<PreviewPlumbing>(cursor, state)
  }
}

macro_rules! impl_formattable_delegate {
  ($T:ident for $Type:ty) => (
    impl<$T: Formattable<State> + ?Sized, State: Clone> Formattable<State> for $Type {
      type Layout = $T::Layout;

      fn pick_layout(&self, cursor: Cursor, state: State) -> Self::Layout {
        $T::pick_layout(self, cursor, state)
      }

      fn format(&self, formatter: &mut (impl Formatter + ?Sized), layout: Self::Layout, state: State) {
        $T::format(self, formatter, layout, state);
      }

      fn format_to<P>(&self, cursor: Cursor, layout: Self::Layout, state: State) -> P::Output
      where P: Plumbing + Default {
        $T::format_to::<P>(self, cursor, layout, state)
      }

      fn format_to_string(&self, cursor: Cursor, layout: Self::Layout, state: State) -> String {
        $T::format_to_string(self, cursor, layout, state)
      }

      fn format_to_preview(&self, cursor: Cursor, layout: Self::Layout, state: State) -> Preview {
        $T::format_to_preview(self, cursor, layout, state)
      }

      fn format_auto(&self, formatter: &mut (impl Formatter + ?Sized), state: State) {
        $T::format_auto(self, formatter, state);
      }

      fn format_to_auto<P>(&self, cursor: Cursor, state: State) -> P::Output
      where P: Plumbing + Default {
        $T::format_to_auto::<P>(self, cursor, state)
      }

      fn format_to_string_auto(&self, cursor: Cursor, state: State) -> String {
        $T::format_to_string_auto(self, cursor, state)
      }

      fn format_to_preview_auto(&self, cursor: Cursor, state: State) -> Preview {
        $T::format_to_preview_auto(self, cursor, state)
      }
    }
  );
}

impl_formattable_delegate!(T for &T);
impl_formattable_delegate!(T for &mut T);
impl_formattable_delegate!(T for Box<T>);
impl_formattable_delegate!(T for std::rc::Rc<T>);
impl_formattable_delegate!(T for std::sync::Arc<T>);

/// If you want to implement [`Formattable`] for a type that implements [`Printable`] for whatever reason,
/// you can use this macro to implement it easily.
#[macro_export]
macro_rules! impl_formattable_from_printable {
  ($Type:ty) => (
    impl<State: Clone> $crate::format::Formattable<State> for $Type {
      $crate::formattable_unit_layout!(State);

      fn format(&self, formatter: &mut (impl $crate::format::Formatter + ?Sized), _: (), _: State) {
        <$Type as $crate::sink::Printable>::print(self, formatter)
      }
    }
  );
}

/// Expands to all of the items necessary to specify a 'unit layout' (one possible layout) in a [`Formattable`] implementation.
///
/// # Example
/// ```rust
/// # use shapeshifter::format::*;
/// # use shapeshifter::sink::*;
/// struct MyStruct;
///
/// impl<State: Clone> Formattable<State> for MyStruct {
///   shapeshifter::formattable_unit_layout!(State);
///
///   fn format(&self, formatter: &mut impl Formatter, layout: (), state: State) {
///     todo!();
///   }
/// }
/// ```
#[macro_export]
macro_rules! formattable_unit_layout {
  ($State:ty) => (
    type Layout = ();

    #[inline]
    fn pick_layout(&self, _: $crate::format::Cursor, _: $State) -> () { () }
  );
}



/// An extension of the [`Sink`] trait that contains extra state for adaptive formatting within a [`Formattable`] implementation.
///
/// The [`Formatter`] trait is akin to [`fmt::Formatter`][std::fmt::Formatter], but it is a subtrait
/// of [`Sink`] rather than implementing [`fmt::Write`][std::fmt::Write] (see [`Sink`] for more information).
///
/// If you are using the default [`Formatter`], [`GenericFormatter`] (you probably are), it performs the following input transformation:
/// - When the tab (`\t`) character is written, the configured [`Indent`] described by the current [`Cursor`] is written instead.
/// - When the newline (`\n`) character is written, the configured [`Newline`] described by the current [`Cursor`] is written instead,
///   and the appropriate number of [`Indent`]s are added to return to the current indent level.
pub trait Formatter: Sink {
  /// Gets the [`Cursor`] belonging to this [`Formatter`].
  fn cursor(&self) -> Cursor;

  /// Gets a mutable reference to the [`Cursor`] belonging to this [`Formatter`].
  fn cursor_mut(&mut self) -> &mut Cursor;

  /// Convenience function that increments the indent counter before executing the given function, and decrements it afterwards.
  fn indent(&mut self, f: impl FnOnce(&mut Self)) {
    self.cursor_mut().increment_indent();
    f(self);
    self.cursor_mut().decrement_indent();
  }

  /// Convenience function that allows printing a value delimited on either side by [`Printable`] items.
  fn delimit(
    &mut self,
    start: impl Printable,
    end: impl Printable,
    f: impl FnOnce(&mut Self)
  ) {
    start.print(self);
    f(self);
    end.print(self);
  }

  /// Convenience function that prints a series of values separated by a [`Printable`] item.
  fn separate<I>(
    &mut self,
    separator: impl Printable,
    include_trailing: bool,
    values: I,
    f: impl FnMut(&mut Self, <I as IntoIterator>::Item)
  ) where I: IntoIterator {
    let trailing_separator = if include_trailing { Some(&separator) } else { None };
    self.separate_alt(&separator, trailing_separator, values, f);
  }

  /// Convenience function that prints a series of values separated by a [`Printable`] item.
  fn separate_alt<I>(
    &mut self,
    separator: impl Printable,
    trailing_separator: Option<impl Printable>,
    values: I,
    mut f: impl FnMut(&mut Self, <I as IntoIterator>::Item)
  ) where I: IntoIterator {
    for (i, value) in values.into_iter().enumerate() {
      if i != 0 { separator.print(self); };
      f(self, value);
    };

    if let Some(trailing_separator) = trailing_separator {
      trailing_separator.print(self);
    };
  }
}

macro_rules! impl_formatter_delegate {
  ($T:ident for $Type:ty) => (
    impl<$T: Formatter + ?Sized> Formatter for $Type {
      #[inline]
      fn cursor(&self) -> Cursor {
        $T::cursor(self)
      }

      #[inline]
      fn cursor_mut(&mut self) -> &mut Cursor {
        $T::cursor_mut(self)
      }
    }
  );
}

impl_formatter_delegate!(T for &mut T);
impl_formatter_delegate!(T for Box<T>);



/// A wrapper type that allows input to be passed to a [`Formatter`] without input transformation.
///
/// Currently, [`RawMode`] is only supported by [`GenericFormatter`]
/// (or any other [`Formatter`] `F` that implements `Sink for RawMode<F>`).
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct RawMode<F: ?Sized>(F);

unsafe impl<F: ?Sized> TransparentWrapper<F> for RawMode<F> {}



/// A [`Formatter`] that produces a [`String`].
pub type BufferFormatter = GenericFormatter<StringPlumbing>;
/// A [`Formatter`] that produces a [`Preview`].
pub type PreviewFormatter = GenericFormatter<PreviewPlumbing>;

/// A general-use [`Formatter`] that performs input transformation.
///
/// This formatter performs the following input transformation:
/// - When the tab (`\t`) character is written, the configured [`Indent`] described by the current [`Cursor`] is written instead.
/// - When the newline (`\n`) character is written, the configured [`Newline`] described by the current [`Cursor`] is written instead,
///   and the appropriate number of [`Indent`]s are added to return to the current indent level.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GenericFormatter<P: Plumbing> {
  cursor: Cursor,
  plumbing: P
}

impl<P: Plumbing> GenericFormatter<P> {
  /// Creates a new [`GenericFormatter`], given a [`Cursor`].
  pub fn new(cursor: Cursor) -> Self where P: Default {
    Self::with_plumbing(cursor, P::default())
  }

  /// Creates a new [`GenericFormatter`], given a [`Cursor`] and a [`Plumbing`].
  pub const fn with_plumbing(cursor: Cursor, plumbing: P) -> Self {
    GenericFormatter { cursor, plumbing }
  }

  /// Extract the [`Cursor`] and [`Plumbing`] from this [`GenericFormatter`].
  pub fn into_inner(self) -> (Cursor, P) {
    (self.cursor, self.plumbing)
  }

  /// Extract the [output type][Plumbing::Output] of this [`GenericFormatter`].
  pub fn into_output(self) -> P::Output {
    self.plumbing.into_output()
  }
}

impl<P: Plumbing> Formatter for GenericFormatter<P> {
  #[inline]
  fn cursor(&self) -> Cursor {
    self.cursor
  }

  #[inline]
  fn cursor_mut(&mut self) -> &mut Cursor {
    &mut self.cursor
  }
}

impl<P: Plumbing> Sink for GenericFormatter<P> {
  fn write_char(&mut self, c: char) {
    self.plumbing.accept_char(&mut self.cursor, c);
  }
}



/// A [`Plumbing`] that produces a [`String`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringPlumbing {
  string: String
}

impl StringPlumbing {
  /// Creates a new [`StringPlumbing`].
  pub const fn new() -> Self {
    StringPlumbing { string: String::new() }
  }

  /// Consumes this [`StringPlumbing`] and extracts the underlying [`String`].
  pub fn into_string(self) -> String {
    self.string
  }
}

impl Default for StringPlumbing {
  fn default() -> Self {
    Self::new()
  }
}

impl Plumbing for StringPlumbing {
  type Output = String;

  fn into_output(self) -> Self::Output {
    self.into_string()
  }

  fn accept_raw(&mut self, printable: impl PrintableKnownLen) {
    printable.print(&mut self.string);
  }

  fn accept_newline(&mut self, newline: Newline) {
    newline.print(&mut self.string);
  }
}



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

/// A [`Plumbing`] that produces a [`Preview`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PreviewPlumbing {
  len: usize,
  vertical_span: usize,
  horizontal_span: usize,
  current_column: usize
}

impl PreviewPlumbing {
  /// Creates a new [`PreviewPlumbing`].
  pub const fn new() -> Self {
    PreviewPlumbing {
      len: 0,
      vertical_span: 1,
      horizontal_span: 0,
      current_column: 0
    }
  }

  /// Consumes this [`PreviewPlumbing`] and extracts its [`Preview`] information.
  pub fn into_preview(self) -> Preview {
    let horizontal_span = usize::max(self.horizontal_span, self.current_column);
    Preview { len: self.len, vertical_span: self.vertical_span, horizontal_span }
  }
}

impl Default for PreviewPlumbing {
  fn default() -> Self {
    Self::new()
  }
}

impl Plumbing for PreviewPlumbing {
  type Output = Preview;

  fn into_output(self) -> Self::Output {
    self.into_preview()
  }

  fn accept_raw(&mut self, printable: impl PrintableKnownLen) {
    let len = printable.print_len();
    self.len += len;
    self.current_column += len;
  }

  fn accept_newline(&mut self, newline: Newline) {
    let column = std::mem::take(&mut self.current_column);
    self.len += newline.print_len();
    self.vertical_span += 1;
    self.horizontal_span = usize::max(self.horizontal_span, column);
    self.current_column = 0;
  }
}



/// Handles input transformation within a [`GenericFormatter`].
///
/// This is primarily an implementation detail, and you likely do not need a [`Plumbing`].
pub trait Plumbing {
  /// The output type of this [`Plumbing`].
  type Output;

  /// Convert this [`Plumbing`] into its output type.
  fn into_output(self) -> Self::Output;

  /// Accepts some input (in the form of a [`PrintableKnownLen`]) without transforming it.
  fn accept_raw(&mut self, printable: impl PrintableKnownLen);

  /// Accepts a single newline.
  fn accept_newline(&mut self, newline: Newline);

  /// Accepts a pending indent, if possible. (See [Cursor::pending_indent])
  ///
  /// This function should be called before writing anything.
  fn accept_pending_indent(&mut self, cursor: &mut Cursor) {
    if std::mem::take(&mut cursor.pending_indent) {
      self.accept_raw(Repeat::new(cursor.indent, cursor.indent_level));
    }
  }

  /// Accepts a single character, performing input transformation.
  fn accept_char(&mut self, cursor: &mut Cursor, c: char) {
    match c {
      '\n' => {
        self.accept_newline(cursor.newline);
        cursor.pending_indent = true;
      },
      '\t' => {
        self.accept_pending_indent(cursor);
        self.accept_raw(cursor.indent);
      },
      c => {
        self.accept_pending_indent(cursor);
        self.accept_raw(c);
      }
    };
  }
}
