/// A trait for endian writers to allow interchangeable usage.
pub trait EndianWriterTrait {
    /// Writes a byte slice to the current position and advances the pointer.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it writes directly to memory without bounds checking.
    /// The caller must ensure that there's enough space to write all the bytes in the slice.
    ///
    /// # Parameters
    ///
    /// * `data`: A slice of bytes to be written.
    unsafe fn write_bytes(&mut self, data: &[u8]);

    /// Advances the internal pointer by the specified offset.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it modifies the internal pointer without bounds checking.
    /// The caller must ensure that the new pointer position is valid.
    ///
    /// # Parameters
    ///
    /// * `offset`: The number of bytes to advance the pointer.
    unsafe fn seek(&mut self, offset: isize);
}

/// A trait for endian readers to allow interchangeable usage.
pub trait EndianReaderTrait {
    /// Reads a byte slice from the current position and advances the pointer.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it reads directly from memory without bounds checking.
    /// The caller must ensure that there's enough data to read all the bytes into the slice.
    ///
    /// # Parameters
    ///
    /// * `data`: A mutable slice to read the bytes into.
    unsafe fn read_bytes(&mut self, data: &mut [u8]);

    /// Advances the internal pointer by the specified offset.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it modifies the internal pointer without bounds checking.
    /// The caller must ensure that the new pointer position is valid.
    ///
    /// # Parameters
    ///
    /// * `offset`: The number of bytes to advance the pointer.
    unsafe fn seek(&mut self, offset: isize);
}

/// A trait for types that can determine their serialized size in bytes.
///
/// **Note:** This size may differ from the native struct size due to custom serialization logic,
/// such as bit-packing or padding.
///
/// Implementers must ensure that `size_in_bytes` accurately reflects the number of bytes
/// the type occupies when serialized to a pointer.
pub trait HasSize {
    /// Returns the serialized size of the type in bytes.
    fn size_in_bytes() -> usize;
}

macro_rules! impl_has_size {
    ($($t:ty),*) => {
        $(
            impl HasSize for $t {
                #[inline(always)]
                fn size_in_bytes() -> usize {
                    core::mem::size_of::<$t>()
                }
            }
        )*
    };
}

impl_has_size!(i8, u8, i16, u16, i32, u32, i64, u64, f32, f64);
