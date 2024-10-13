use crate::{EndianReaderTrait, HasSize};
use core::mem::size_of;
use core::ptr::{copy_nonoverlapping, read_unaligned};

/// A trait for types that can be read in little-endian format from the current position.
///
/// # Examples
///
/// Implementing `ReadLittleEndian` for `u32`:
///
/// ```compile_fail
/// use endian_writer::LittleEndianReader;
/// use endian_writer::ReadLittleEndian;
/// use core::mem::size_of;
/// use core::ptr::read_unaligned;
///
/// impl ReadLittleEndian for u32 {
///     unsafe fn read_le(reader: &mut LittleEndianReader) -> Self {
///         let value = read_unaligned(reader.ptr as *const u32);
///         reader.ptr = reader.ptr.add(size_of::<u32>());
///         Self::from_le(value)
///     }
/// }
/// ```
pub trait ReadLittleEndian {
    /// Reads the value in little-endian format from the current position.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it reads directly from memory without bounds checking.
    /// The caller must ensure that the reader has enough data to read the value.
    unsafe fn read_le(reader: &mut LittleEndianReader) -> Self;
}

/// A trait for types that can be read in little-endian format from a specified offset.
/// The reader is not advanced.
///
/// # Examples
///
/// Implementing `ReadLittleEndianAtOffset` for `u32`:
///
/// ```compile_fail
/// use endian_writer::LittleEndianReader;
/// use endian_writer::ReadLittleEndianAtOffset;
/// use core::mem::size_of;
/// use core::ptr::read_unaligned;
///
/// impl ReadLittleEndianAtOffset for u32 {
///     unsafe fn read_at_offset_le(reader: &mut LittleEndianReader, offset_in_bytes: isize) -> Self {
///         let value = read_unaligned(reader.ptr.offset(offset_in_bytes) as *const u32);
///         Self::from_le(value)
///     }
/// }
/// ```
pub trait ReadLittleEndianAtOffset {
    /// Reads the value in little-endian format from the specified offset.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it reads directly from memory without bounds checking.
    /// The caller must ensure that the reader has enough data to read the value at the given offset.
    ///
    /// # Parameters
    ///
    /// * `reader`: The [LittleEndianReader] to read from.
    /// * `offset_in_bytes`: The offset in number of bytes from the current position.
    unsafe fn read_at_offset_le(reader: &mut LittleEndianReader, offset_in_bytes: isize) -> Self;
}

/// A utility for reading data in little-endian format from a raw pointer.
#[derive(Debug)]
pub struct LittleEndianReader {
    pub ptr: *const u8,
}

impl LittleEndianReader {
    /// Creates a new [LittleEndianReader] with the given raw pointer.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the provided pointer is valid and points to enough
    /// allocated memory for the intended read operations.
    ///
    /// # Parameters
    ///
    /// * `ptr`: A raw const pointer to the memory location from where data will be read.
    pub unsafe fn new(ptr: *const u8) -> Self {
        LittleEndianReader { ptr }
    }

    /// Reads a value from the current position and advances the pointer.
    ///
    /// This method can read any type that implements the `ReadLittleEndian` trait.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it reads directly from memory without bounds checking.
    /// The caller must ensure that there's enough data to read the value.
    ///
    /// # Type Parameters
    ///
    /// * `T`: The type of value to read, which must implement `ReadLittleEndian`.
    ///
    /// # Returns
    ///
    /// The value read from memory, interpreted in little-endian format.
    #[inline(always)]
    pub unsafe fn read<T: ReadLittleEndian>(&mut self) -> T {
        T::read_le(self)
    }

    /// Reads a value at the specified offset without advancing the pointer.
    ///
    /// This method can read any type that implements the `ReadLittleEndianAtOffset` trait.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it reads directly from memory without bounds checking.
    /// The caller must ensure that there's enough data to read the value at the given offset.
    ///
    /// # Type Parameters
    ///
    /// * `T`: The type of value to read, which must implement `ReadLittleEndianAtOffset`.
    ///
    /// # Parameters
    ///
    /// * `offset_in_bytes`: The offset in number of bytes from the current position.
    ///
    /// # Returns
    ///
    /// The value read from memory at the specified offset, interpreted in little-endian format.
    #[inline(always)]
    pub unsafe fn read_at_offset<T: ReadLittleEndianAtOffset>(
        &mut self,
        offset_in_bytes: isize,
    ) -> T {
        T::read_at_offset_le(self, offset_in_bytes)
    }

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
    #[inline(always)]
    pub unsafe fn read_bytes(&mut self, data: &mut [u8]) {
        copy_nonoverlapping(self.ptr, data.as_mut_ptr(), data.len());
        self.ptr = self.ptr.add(data.len());
    }

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
    #[inline(always)]
    pub unsafe fn seek(&mut self, offset: isize) {
        self.ptr = self.ptr.offset(offset);
    }
}

impl EndianReaderTrait for LittleEndianReader {
    unsafe fn read_bytes(&mut self, data: &mut [u8]) {
        self.read_bytes(data)
    }

    unsafe fn seek(&mut self, offset: isize) {
        self.seek(offset)
    }
}

/// Blanket implementation: Automatically implement `ReadLittleEndian` for any type
/// that implements `ReadLittleEndianAtOffset` and `HasSize`.
impl<T> ReadLittleEndian for T
where
    T: ReadLittleEndianAtOffset + HasSize,
{
    #[inline(always)]
    unsafe fn read_le(reader: &mut LittleEndianReader) -> Self {
        // Read at current position (offset 0)
        let result = T::read_at_offset_le(reader, 0);
        // Advance the reader's pointer by the serialized size
        reader.seek(T::size_in_bytes() as isize);
        result
    }
}

// Implement ReadLittleEndian for various integer types
macro_rules! impl_read_little_endian {
    ($($t:ty),*) => {
        $(
            impl ReadLittleEndianAtOffset for $t {
                #[inline(always)]
                #[allow(clippy::size_of_in_element_count)]
                unsafe fn read_at_offset_le(reader: &mut LittleEndianReader, offset_in_bytes: isize) -> Self {
                    let value = read_unaligned(reader.ptr.offset(offset_in_bytes) as *const $t);
                    <$t>::from_le(value)
                }
            }
        )*
    };
}

impl_read_little_endian!(i8, u8, i16, u16, i32, u32, i64, u64);

// Special implementation for floating-point types
macro_rules! impl_read_little_endian_float {
    ($($t:ty),*) => {
        $(
            impl ReadLittleEndianAtOffset for $t {
                #[inline(always)]
                unsafe fn read_at_offset_le(reader: &mut LittleEndianReader, offset_in_bytes: isize) -> Self {
                    let mut bytes = [0u8; size_of::<$t>()];
                    copy_nonoverlapping(
                        reader.ptr.offset(offset_in_bytes),
                        bytes.as_mut_ptr(),
                        size_of::<$t>()
                    );
                    <$t>::from_le_bytes(bytes)
                }
            }
        )*
    };
}

impl_read_little_endian_float!(f32, f64);

#[cfg(test)]
mod tests {
    use super::*;
    use core::f32;

    #[test]
    fn little_endian_reader_int() {
        let data: [u8; 8] = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]; // little-endian for 0x0807060504030201u64
        let mut reader = unsafe { LittleEndianReader::new(data.as_ptr()) };
        let value: u64 = unsafe { reader.read() };
        assert_eq!(value, 0x0807060504030201);
    }

    #[test]
    fn little_endian_reader_at_offset() {
        let data: [u8; 12] = [
            0x01, 0x02, 0x03, 0x04, // 0x04030201u32
            0xAA, 0xBB, 0xCC, 0xDD, // offset part
            0x05, 0x06, 0x07, 0x08, // 0x08070605u32
        ];
        let mut reader = unsafe { LittleEndianReader::new(data.as_ptr()) };
        let value: u32 = unsafe { reader.read_at_offset(8) };
        assert_eq!(value, 0x08070605);
    }

    #[test]
    fn little_endian_reader_float() {
        let data: [u8; 4] = [0xDB, 0x0F, 0x49, 0x40]; // little-endian for 3.1415927f32
        let mut reader = unsafe { LittleEndianReader::new(data.as_ptr()) };
        let value: f32 = unsafe { reader.read() };
        assert!((value - f32::consts::PI).abs() < f32::EPSILON); // Compare with tolerance for floating-point values
    }

    #[test]
    fn little_endian_reader_at_offset_float() {
        let data: [u8; 12] = [
            0x01, 0x02, 0x03, 0x04, // 0x04030201u32
            0xAA, 0xBB, 0xCC, 0xDD, // offset part
            0xDB, 0x0F, 0x49, 0x40, // little-endian for 3.1415927f32
        ];
        let mut reader = unsafe { LittleEndianReader::new(data.as_ptr()) };
        let value: f32 = unsafe { reader.read_at_offset(8) };
        assert!((value - f32::consts::PI).abs() < f32::EPSILON);
    }
}
