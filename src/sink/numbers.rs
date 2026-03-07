use itoa::Buffer;



crate::impl_printable_from_display!(f32);
crate::impl_printable_from_display!(f64);

macro_rules! impl_printable_integer_unsigned {
  ($Type:ty) => (
    impl $crate::sink::Printable for $Type {
      #[inline]
      fn print(&self, sink: &mut (impl $crate::sink::Sink + ?Sized)) {
        sink.write_str(Buffer::new().format(*self))
      }
    }

    impl $crate::sink::PrintableKnownLen for $Type {
      #[inline]
      fn print_len(&self) -> usize {
        self.checked_ilog10().unwrap_or(0) as usize + 1
      }
    }
  );
}

macro_rules! impl_printable_integer_signed {
  ($Type:ty) => (
    impl $crate::sink::Printable for $Type {
      #[inline]
      fn print(&self, sink: &mut (impl $crate::sink::Sink + ?Sized)) {
        sink.write_str(Buffer::new().format(*self))
      }
    }

    impl $crate::sink::PrintableKnownLen for $Type {
      #[inline]
      fn print_len(&self) -> usize {
        self.abs_diff(0).checked_ilog10().unwrap_or(0) as usize
          + if self.is_negative() { 2 } else { 1 }
      }
    }
  );
}

impl_printable_integer_unsigned!(u8);
impl_printable_integer_unsigned!(u16);
impl_printable_integer_unsigned!(u32);
impl_printable_integer_unsigned!(u64);
impl_printable_integer_unsigned!(u128);
impl_printable_integer_unsigned!(usize);
impl_printable_integer_signed!(i8);
impl_printable_integer_signed!(i16);
impl_printable_integer_signed!(i32);
impl_printable_integer_signed!(i64);
impl_printable_integer_signed!(i128);
impl_printable_integer_signed!(isize);
