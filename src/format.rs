//! Internals relating to [`Formattable`] and [`Formatter`].

use crate::primitive::*;

use std::fmt;



/// Something that holds a [`Config`].
pub trait WithConfig {
  /// Get the [`Config`].
  fn config(&self) -> Config;
}

impl WithConfig for Config {
  fn config(&self) -> Config {
    *self
  }
}

impl<T> WithConfig for &T where T: WithConfig + ?Sized {
  fn config(&self) -> Config {
    T::config(self)
  }
}

impl<T> WithConfig for &mut T where T: WithConfig + ?Sized {
  fn config(&self) -> Config {
    T::config(self)
  }
}

/// Preferences for what type of indentation and newline should be used when printing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Config {
  /// What should be written when indenting.
  pub indent: Indent,
  /// What should be written to the sink whenever a newline is encountered.
  pub newline: Newline
}

impl Config {
  /// Tab character (`'\t'`) as indent, with Unix-style line endings.
  pub const DEFAULT_UNIX_TABS: Self = Config::new(Indent::TABS, Newline::LF);
  /// Tab character (`'\t'`) as indent, with Windows-style line endings.
  pub const DEFAULT_WIN_TABS: Self = Config::new(Indent::TABS, Newline::CRLF);
  /// Two spaces per indent, with Unix-style line endings.
  pub const DEFAULT_UNIX_SPACES2: Self = Config::new(Indent::SPACES2, Newline::LF);
  /// Two spaces per indent, with Windows-style line endings.
  pub const DEFAULT_WIN_SPACES2: Self = Config::new(Indent::SPACES2, Newline::CRLF);
  /// Four spaces per indent, with Unix-style line endings.
  pub const DEFAULT_UNIX_SPACES4: Self = Config::new(Indent::SPACES4, Newline::LF);
  /// Four spaces per indent, with Windows-style line endings.
  pub const DEFAULT_WIN_SPACES4: Self = Config::new(Indent::SPACES4, Newline::CRLF);
  /// Eight spaces per indent, with Unix-style line endings.
  pub const DEFAULT_UNIX_SPACES8: Self = Config::new(Indent::SPACES8, Newline::LF);
  /// Eight spaces per indent, with Windows-style line endings.
  pub const DEFAULT_WIN_SPACES8: Self = Config::new(Indent::SPACES8, Newline::CRLF);

  /// Creates a new config.
  pub const fn new(indent: Indent, newline: Newline) -> Config {
    Config { indent, newline }
  }
}



/// Something that holds a [`Location`].
pub trait WithLocation {
  /// Get the [`Location`] immutably.
  fn location(&self) -> &Location;

  /// Get the [`Location`] mutably.
  fn location_mut(&mut self) -> &mut Location;
}

impl WithLocation for Location {
  fn location(&self) -> &Location {
    self
  }

  fn location_mut(&mut self) -> &mut Location {
    self
  }
}

impl<T> WithLocation for &mut T where T: WithLocation + ?Sized {
  fn location(&self) -> &Location {
    T::location(self)
  }

  fn location_mut(&mut self) -> &mut Location {
    T::location_mut(self)
  }
}

/// The internal state of a [`Plumbing`], indicating a number of things about the output
/// produced up to that point, and the current write position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Location {
  /// The total length (in bytes) of the output.
  pub len: usize,
  /// The number of rows spanned by the output.
  pub spanned_width: usize,
  /// The number of columns spanned by the output, i.e. the length of the longest row.
  pub spanned_height: usize,
  /// The current column position.
  pub current_column: usize,
  /// The current indent level.
  pub indent_level: usize,
  /// Whether or not a lazy indentation is pending.
  pub pending_indent: bool
}

impl Location {
  const fn new() -> Self {
    Location {
      len: 0,
      spanned_width: 0,
      spanned_height: 0,
      current_column: 0,
      indent_level: 0,
      pending_indent: false
    }
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

  /// Apply input to this [`Location`].
  pub fn apply_input(&mut self, len: usize) {
    self.len += len;
    self.current_column += len;
    self.spanned_width = self.spanned_width.max(self.current_column);
  }

  /// Apply a newline to this [`Location`].
  pub fn apply_newline(&mut self, len: usize) {
    self.len += len;
    self.apply_input(0);
    self.spanned_height += 1;
    self.current_column = 0;
  }
}



impl WithConfig for (Config, Location) {
  fn config(&self) -> Config {
    self.0
  }
}

impl WithLocation for (Config, Location) {
  fn location(&self) -> &Location {
    &self.1
  }

  fn location_mut(&mut self) -> &mut Location {
    &mut self.1
  }
}



/// Describes how a type can be adaptively formatted as text.
///
/// The [`Formattable`] trait takes a custom `State` parameter that allows
/// the user to pass around custom state, such as formatting preferences.
///
/// A [`Formattable`] implementation requires an associated `Layout` type, which encodes the totality of
/// ways in which the value may be formatted. When formatting automatically (via [`format_auto`][FormattableExt::format_auto]
/// or otherwise), it will pick a layout mode itself with the [`pick_layout`][Formattable::pick_layout] method,
/// which specifies what layout mode should be used for the given item in the given scenario.
///
/// Most methods on [`Formattable`] pass in a [`Formatter`] which is akin to [`fmt::Formatter`][std::fmt::Formatter],
/// and implements [`fmt::Write`], with a few caveats.
///
/// ## Usage
/// - If you are implementing this trait yourself, you only need to implement the
///   [`format`][Formattable::format] and [`pick_layout`][Formattable::pick_layout] methods.
/// - If you are trying to format a value within a [`Formattable`] implementation, you likely want to use
///   [`format`][Formattable::format] or [`format_auto`][FormattableExt::format_auto] depending on whether the formatter
///   should pick a layout for you, or you would like to specify one yourself.
/// - If you are trying to produce a preview for use inside [`pick_layout`][Formattable::pick_layout], only
///   use [`format_to_preview`][FormattableExt::format_to_preview], as [`format_to_preview_auto`][FormattableExt::format_to_preview_auto]
///   calls [`pick_layout`][Formattable::pick_layout] itself to determine the layout mode and will cause an infinite loop.
/// - If you are trying to produce a final output string for your type, use [`format_to_string_auto`][FormattableExt::format_to_string_auto].
pub trait Formattable<State: Clone>: Sized {
  /// The set of layout modes by which a [`Formattable`] type can be formatted.
  type Layout;

  /// Picks an appropriate layout mode to format the current item with, given the current state.
  fn pick_layout(&self, formatter: &impl Formatter, state: State) -> Result<Self::Layout, fmt::Error>;

  /// Writes the given value into the formatter with the given layout mode.
  fn format(&self, formatter: &mut impl Formatter, layout: Self::Layout, state: State) -> fmt::Result;
}



/// Extension methods for [`Formattable`].
pub trait FormattableExt<State: Clone>: Formattable<State> {
  /// Performs a formatting job, producing its output, given a [`Plumbing`].
  fn format_to<P>(&self, config: Config, layout: Self::Layout, state: State) -> Result<P::Output, fmt::Error>
  where P: Plumbing + Default {
    let mut formatter = GenericFormatter::<P>::new(config);
    self.format(&mut formatter, layout, state)?;
    Ok(formatter.into_output())
  }

  /// Performs a formatting job, producing its output, given a [`Plumbing`], copying the state of another formatter.
  fn format_to_forked<P>(&self, formatter: &impl Formatter, layout: Self::Layout, state: State) -> Result<P::Output, fmt::Error>
  where P: Plumbing + Default {
    let mut formatter = GenericFormatter::<P>::fork(formatter);
    self.format(&mut formatter, layout, state)?;
    Ok(formatter.into_output())
  }

  /// Writes the given value into a string buffer with the given layout mode.
  ///
  /// This function is equivalent to `self.format_to::<StringPlumbing>(config, layout, state)`.
  #[inline]
  fn format_to_string(&self, config: Config, layout: Self::Layout, state: State) -> Result<String, fmt::Error> {
    self.format_to::<StringPlumbing>(config, layout, state)
  }

  /// Writes the given value into a string buffer with the given layout mode, copying the state of another formatter.
  ///
  /// If you'd just like the final printed output, consider using [`FormattableExt::format_to_string`] instead.
  ///
  /// This function is equivalent to `self.format_to_forked::<StringPlumbing>(formatter, layout, state)`.
  fn format_to_string_forked(&self, formatter: &impl Formatter, layout: Self::Layout, state: State) -> Result<String, fmt::Error> {
    self.format_to_forked::<StringPlumbing>(formatter, layout, state)
  }

  /// Produces a 'preview' of how the given value will be formatted with the given layout mode.
  ///
  /// If you'd like to preview a layout mode, consider using [`FormattableExt::format_to_preview_forked`] instead.
  ///
  /// This function is equivalent to `self.format_to::<PreviewPlumbing>(config, layout, state)`.
  #[inline]
  fn format_to_preview(&self, config: Config, layout: Self::Layout, state: State) -> Result<Preview, fmt::Error> {
    self.format_to::<PreviewPlumbing>(config, layout, state)
  }

  /// Produces a 'preview' of how the given value will be formatted with the given layout mode, copying the state of another formatter.
  ///
  /// This is useful for estimating the final length of a line for a layout mode.
  ///
  /// This function is equivalent to `self.format_to_forked::<PreviewPlumbing>(formatter, layout, state)`.
  #[inline]
  fn format_to_preview_forked(&self, formatter: &impl Formatter, layout: Self::Layout, state: State) -> Result<Preview, fmt::Error> {
    self.format_to_forked::<PreviewPlumbing>(formatter, layout, state)
  }

  /// Writes the given value into the formatter, picking layout modes automatically.
  ///
  /// This function is equivalent to `self.format(formatter, self.pick_layout(formatter, state.clone())?, state)`.
  #[inline]
  fn format_auto(&self, formatter: &mut impl Formatter, state: State) -> fmt::Result {
    self.format(formatter, self.pick_layout(formatter, state.clone())?, state)
  }

  /// Performs a formatting job, producing its output, given a [`Plumbing`], picking layout modes automatically.
  ///
  /// This function is equivalent to `self.format_to::<P>(config, self.pick_layout(formatter, state.clone())?, state)`.
  #[inline]
  fn format_to_auto<P>(&self, config: Config, state: State) -> Result<P::Output, fmt::Error>
  where P: Plumbing + Default {
    let mut formatter = GenericFormatter::<P>::new(config);
    let layout = self.pick_layout(&formatter, state.clone())?;
    self.format(&mut formatter, layout, state)?;
    Ok(formatter.into_output())
  }

  /// Performs a formatting job, producing its output, given a [`Plumbing`], picking layout modes automatically.
  ///
  /// This function is equivalent to `self.format_to_forked::<P>(formatter, self.pick_layout(formatter, state.clone())?, state)`.
  #[inline]
  fn format_to_auto_forked<P>(&self, formatter: &impl Formatter, state: State) -> Result<P::Output, fmt::Error>
  where P: Plumbing + Default {
    let mut formatter = GenericFormatter::<P>::fork(formatter);
    let layout = self.pick_layout(&formatter, state.clone())?;
    self.format(&mut formatter, layout, state)?;
    Ok(formatter.into_output())
  }

  /// Writes the given value into a string buffer, picking layout modes automatically.
  ///
  /// This function is equivalent to `self.format_to_auto::<StringPlumbing>(config, state)`.
  #[inline]
  fn format_to_string_auto(&self, config: Config, state: State) -> Result<String, fmt::Error> {
    self.format_to_auto::<StringPlumbing>(config, state)
  }

  /// Writes the given value into a string buffer, picking layout modes automatically.
  ///
  /// This function is equivalent to `self.format_to_auto_forked::<StringPlumbing>(formatter, state)`.
  #[inline]
  fn format_to_string_auto_forked(&self, formatter: &impl Formatter, state: State) -> Result<String, fmt::Error> {
    self.format_to_auto_forked::<StringPlumbing>(formatter, state)
  }

  /// Produces a 'preview' of how the given value will be formatted, picking layout modes automatically.
  ///
  /// This function is equivalent to `self.format_to_auto::<PreviewPlumbing>(config, state)`.
  #[inline]
  fn format_to_preview_auto(&self, config: Config, state: State) -> Result<Preview, fmt::Error> {
    self.format_to_auto::<PreviewPlumbing>(config, state)
  }

  /// Produces a 'preview' of how the given value will be formatted, picking layout modes automatically.
  ///
  /// This function is equivalent to `self.format_to_auto::<PreviewPlumbing>(formatter, state)`.
  #[inline]
  fn format_to_preview_auto_forked(&self, formatter: &impl Formatter, state: State) -> Result<Preview, fmt::Error> {
    self.format_to_auto_forked::<PreviewPlumbing>(formatter, state)
  }
}

impl<State: Clone, T> FormattableExt<State> for T where T: Formattable<State> {}

macro_rules! impl_formattable_delegate {
  ($T:ident for $Type:ty) => ();
}

impl_formattable_delegate!(T for &T);
impl_formattable_delegate!(T for &mut T);
impl_formattable_delegate!(T for Box<T>);
impl_formattable_delegate!(T for std::rc::Rc<T>);
impl_formattable_delegate!(T for std::sync::Arc<T>);

/// Expands to all of the items necessary to specify a 'unit layout' (one possible layout) in a [`Formattable`] implementation.
///
/// # Example
/// ```rust
/// # use shapeshifter::*;
/// # use std::fmt;
/// struct MyStruct;
///
/// impl<State: Clone> Formattable<State> for MyStruct {
///   shapeshifter::formattable_unit_layout!(State);
///
///   fn format(&self, formatter: &mut impl Formatter, layout: (), state: State) -> std::fmt::Result {
///     todo!();
///   }
/// }
/// ```
#[macro_export]
macro_rules! formattable_unit_layout {
  ($State:ty) => (
    type Layout = ();

    #[inline]
    fn pick_layout(&self, _: $crate::Cursor, _: $State) -> std::fmt::Result { Ok(()) }
  );
}



/// An extension of the [`fmt::Write`] trait that contains extra state for adaptive formatting within a [`Formattable`] implementation.
///
/// If you are using the default [`Formatter`], [`GenericFormatter`] (you probably are), it performs the following input transformation:
/// - When the tab (`\t`) character is written, the configured [`Indent`] described by the current [`Location`] is written instead.
/// - When the newline (`\n`) character is written, the configured [`Newline`] described by the current [`Location`] is written instead,
///   and the appropriate number of [`Indent`]s are added to return to the current indent level.
pub trait Formatter: fmt::Write + WithConfig + WithLocation {
  /// Adds 1 to the current indent level.
  fn increment_indent(&mut self) {
    self.location_mut().increment_indent();
  }

  /// Subtracts 1 from the current indent level.
  fn decrement_indent(&mut self) {
    self.location_mut().decrement_indent();
  }

  /// Convenience function that increments the indent counter before executing the given function, and decrements it afterwards.
  fn indent(&mut self, f: impl FnOnce(&mut Self) -> fmt::Result) -> fmt::Result {
    self.increment_indent();
    f(self)?;
    self.decrement_indent();
    Ok(())
  }

  /// Convenience function that allows printing a value delimited on either side by [`fmt::Display`] items.
  fn delimit(
    &mut self,
    start: impl fmt::Display,
    end: impl fmt::Display,
    f: impl FnOnce(&mut Self) -> fmt::Result
  ) -> fmt::Result {
    self.write_display(&start)?;
    f(self)?;
    self.write_display(&end)?;
    Ok(())
  }

  /// Convenience function that prints a series of values separated by a [`fmt::Display`] item.
  fn separate<I>(
    &mut self,
    separator: impl fmt::Display,
    include_trailing: bool,
    values: I,
    f: impl FnMut(&mut Self, <I as IntoIterator>::Item) -> fmt::Result
  ) -> fmt::Result where I: IntoIterator {
    let trailing_separator = if include_trailing { Some(&separator) } else { None };
    self.separate_alt(&separator, trailing_separator, values, f)
  }

  /// Convenience function that prints a series of values separated by a [`fmt::Display`] item.
  fn separate_alt<I>(
    &mut self,
    separator: impl fmt::Display,
    trailing_separator: Option<impl fmt::Display>,
    values: I,
    mut f: impl FnMut(&mut Self, <I as IntoIterator>::Item) -> fmt::Result
  ) -> fmt::Result where I: IntoIterator {
    for (i, value) in values.into_iter().enumerate() {
      if i != 0 {
        self.write_display(&separator)?;
      };

      f(self, value)?;
    };

    if let Some(trailing_separator) = trailing_separator {
      self.write_display(&trailing_separator)?;
    };

    Ok(())
  }
}

macro_rules! impl_formatter_delegate {
  ($T:ident for $Type:ty) => (
    impl<$T: Formatter + ?Sized> Formatter for $Type {}
  );
}

impl_formatter_delegate!(T for &mut T);



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
  config: Config,
  plumbing: P
}

impl<P: Plumbing> GenericFormatter<P> {
  /// Creates a new [`GenericFormatter`], given a [`Config`].
  pub fn new(config: Config) -> Self where P: Default {
    Self::with_plumbing(config, P::default())
  }

  /// Creates a new [`GenericFormatter`], copying the state of another formatter.
  pub fn fork(formatter: &impl Formatter) -> Self {
    Self::with_plumbing(formatter.config(), P::from(*formatter.location()))
  }

  /// Creates a new [`GenericFormatter`], given a [`Location`] and a [`Plumbing`].
  pub const fn with_plumbing(config: Config, plumbing: P) -> Self {
    GenericFormatter { config, plumbing }
  }

  /// Extract the [`Config`] and [`Plumbing`] from this [`GenericFormatter`].
  pub fn into_inner(self) -> (Config, P) {
    (self.config, self.plumbing)
  }

  /// Extract the [output type][Plumbing::Output] of this [`GenericFormatter`].
  pub fn into_output(self) -> P::Output {
    self.plumbing.into_output()
  }
}

impl<P: Plumbing> Formatter for GenericFormatter<P> {}

impl<P: Plumbing> WithConfig for GenericFormatter<P> {
  fn config(&self) -> Config {
    self.config
  }
}

impl<P: Plumbing> WithLocation for GenericFormatter<P> {
  fn location(&self) -> &Location {
    self.plumbing.location()
  }

  fn location_mut(&mut self) -> &mut Location {
    self.plumbing.location_mut()
  }
}

impl<P: Plumbing> fmt::Write for GenericFormatter<P> {
  fn write_str(&mut self, s: &str) -> fmt::Result {
    for c in s.chars() {
      self.write_char(c)?;
    };
    Ok(())
  }

  fn write_char(&mut self, c: char) -> fmt::Result {
    self.plumbing.accept_char(self.config, c);
    Ok(())
  }
}



/// A [`Plumbing`] that produces a [`String`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringPlumbing {
  location: Location,
  string: String
}

impl StringPlumbing {
  /// Creates a new [`StringPlumbing`].
  pub const fn new() -> Self {
    StringPlumbing::with_location(Location::new())
  }

  /// Create a new [`PreviewPlumbing`] with a [`Location`].
  pub const fn with_location(location: Location) -> Self {
    StringPlumbing { location, string: String::new() }
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

impl From<Location> for StringPlumbing {
  fn from(location: Location) -> Self {
    Self::with_location(location)
  }
}

impl WithLocation for StringPlumbing {
  fn location(&self) -> &Location {
    &self.location
  }

  fn location_mut(&mut self) -> &mut Location {
    &mut self.location
  }
}

impl Plumbing for StringPlumbing {
  type Output = String;

  fn into_output(self) -> Self::Output {
    self.into_string()
  }

  fn accept_char_raw(&mut self, c: char) {
    self.string.push(c);
  }
}



/// The [`Preview`] struct gives you a basic overview of how something will be formatted, at a lower cost.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Preview {
  /// The total length (in bytes) of the output.
  pub len: usize,
  /// The number of rows spanned by the output.
  pub spanned_height: usize,
  /// The number of columns spanned by the output, i.e. the length of the longest row.
  pub spanned_width: usize
}

/// A [`Plumbing`] that produces a [`Preview`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PreviewPlumbing {
  location: Location
}

impl PreviewPlumbing {
  /// Creates a new [`PreviewPlumbing`].
  pub const fn new() -> Self {
    PreviewPlumbing::with_location(Location::new())
  }

  /// Create a new [`PreviewPlumbing`] with a [`Location`].
  pub const fn with_location(location: Location) -> Self {
    PreviewPlumbing { location }
  }

  /// Consumes this [`PreviewPlumbing`] and extracts its [`Preview`] information.
  pub fn into_preview(self) -> Preview {
    let spanned_height = self.location.spanned_height;
    let spanned_width = usize::max(self.location.spanned_width, self.location.current_column);
    Preview { len: self.location.len, spanned_height, spanned_width }
  }
}

impl Default for PreviewPlumbing {
  fn default() -> Self {
    Self::new()
  }
}

impl From<Location> for PreviewPlumbing {
  fn from(location: Location) -> Self {
    Self::with_location(location)
  }
}

impl WithLocation for PreviewPlumbing {
  fn location(&self) -> &Location {
    &self.location
  }

  fn location_mut(&mut self) -> &mut Location {
    &mut self.location
  }
}

impl Plumbing for PreviewPlumbing {
  type Output = Preview;

  fn into_output(self) -> Self::Output {
    self.into_preview()
  }

  fn accept_char_raw(&mut self, _: char) {}
}



/// Handles input transformation within a [`GenericFormatter`].
///
/// This is primarily an implementation detail, and you likely do not need a [`Plumbing`].
pub trait Plumbing: From<Location> + WithLocation {
  /// The output type of this [`Plumbing`].
  type Output;

  /// Convert this [`Plumbing`] into its output type.
  fn into_output(self) -> Self::Output;

  /// Accepts a single indent.
  fn accept_indent(&mut self, indent: Indent) {
    self.location_mut().apply_input(indent.chars_len());

    for c in indent {
      self.accept_char_raw(c);
    };
  }

  /// Accepts a single newline.
  fn accept_newline(&mut self, newline: Newline) {
    self.location_mut().apply_newline(newline.chars_len());

    for c in newline {
      self.accept_char_raw(c);
    };
  }

  /// Accepts a pending indent, if possible. (See [Location::pending_indent])
  ///
  /// This function should be called before writing anything.
  fn accept_pending_indent(&mut self, config: Config) {
    if std::mem::take(&mut self.location_mut().pending_indent) {
      for _ in 0..self.location().indent_level {
        self.accept_indent(config.indent);
      };
    };
  }

  /// Accepts a single character, pushing to any underlying buffer.
  fn accept_char_raw(&mut self, c: char);

  /// Accepts a single character, performing input transformation.
  fn accept_char(&mut self, config: Config, c: char) {
    match c {
      '\n' => {
        self.accept_newline(config.newline);
        self.location_mut().pending_indent = true;
      },
      '\t' => {
        self.accept_pending_indent(config);
        self.accept_indent(config.indent);
      },
      c => {
        self.accept_pending_indent(config);
        self.location_mut().apply_input(1);
        self.accept_char_raw(c);
      }
    };
  }
}
