use crate::{EndianWriterTrait, HasSize};
use core::mem::size_of;
use core::ptr::{copy_nonoverlapping, write_unaligned};

/// A trait for types that can be written in little-endian format at the current position.
///
/// # Examples
///
/// Implementing `WriteLittleEndian` for `u32`:
///
/// ```compile_fail
/// use endian_writer::LittleEndianWriter;
/// use endian_writer::WriteLittleEndian;
/// use core::mem::size_of;
/// use core::ptr::write_unaligned;
///
/// impl WriteLittleEndian for u32 {
///     unsafe fn write_le(self, writer: &mut LittleEndianWriter) {
///         write_unaligned(writer.ptr as *mut u32, self.to_le());
///         writer.ptr = writer.ptr.add(size_of::<u32>());
///     }
/// }
/// ```
pub trait WriteLittleEndian {
    /// Writes the value in little-endian format at the current position.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it writes directly to memory without bounds checking.
    /// The caller must ensure that the writer has enough space to write the value.
    unsafe fn write_le(self, writer: &mut LittleEndianWriter);
}

/// A trait for types that can be written in little-endian format at a specified offset.
/// The writer is not advanced.
///
/// # Examples
///
/// Implementing `WriteLittleEndianAtOffset` for `u32`:
///
/// ```compile_fail
/// use endian_writer::LittleEndianWriter;
/// use endian_writer::WriteLittleEndianAtOffset;
/// use core::mem::size_of;
/// use core::ptr::write_unaligned;
///
/// impl WriteLittleEndianAtOffset for u32 {
///     unsafe fn write_at_offset_le(self, writer: &mut LittleEndianWriter, offset_in_bytes: isize) {
///         write_unaligned(writer.ptr.offset(offset_in_bytes) as *mut u32, self.to_le());
///     }
/// }
/// ```
pub trait WriteLittleEndianAtOffset {
    /// Writes the value in little-endian format at the specified offset.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it writes directly to memory without bounds checking.
    /// The caller must ensure that the writer has enough space to write the value at the given offset.
    ///
    /// # Parameters
    ///
    /// * `writer`: The [LittleEndianWriter] to write to.
    /// * `offset_in_bytes`: The offset in number of bytes from the current position.
    unsafe fn write_at_offset_le(self, writer: &mut LittleEndianWriter, offset_in_bytes: isize);
}

/// A utility for writing data in little-endian format to a raw pointer.
#[derive(Debug)]
pub struct LittleEndianWriter {
    pub ptr: *mut u8,
}

impl LittleEndianWriter {
    /// Creates a new [LittleEndianWriter] with the given raw pointer.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the provided pointer is valid and points to enough
    /// allocated memory for the intended write operations.
    ///
    /// # Parameters
    ///
    /// * `ptr`: A raw mutable pointer to the memory location where data will be written.
    pub unsafe fn new(ptr: *mut u8) -> Self {
        LittleEndianWriter { ptr }
    }

    /// Writes a value to the current position and advances the pointer.
    ///
    /// This method can write any type that implements the `WriteLittleEndian` trait.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it writes directly to memory without bounds checking.
    /// The caller must ensure that there's enough space to write the value.
    ///
    /// # Parameters
    ///
    /// * `value`: The value to be written in little-endian format.
    #[inline(always)]
    pub unsafe fn write<T: WriteLittleEndian>(&mut self, value: T) {
        value.write_le(self);
    }

    /// Writes a value at the specified offset without advancing the pointer.
    ///
    /// This method can write any type that implements the `WriteLittleEndianAtOffset` trait.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it writes directly to memory without bounds checking.
    /// The caller must ensure that there's enough space to write the value at the given offset.
    ///
    /// # Parameters
    ///
    /// * `value`: The value to be written in little-endian format.
    /// * `offset_in_bytes`: The offset in number of bytes from the current position.
    #[inline(always)]
    pub unsafe fn write_at_offset<T: WriteLittleEndianAtOffset>(
        &mut self,
        value: T,
        offset_in_bytes: isize,
    ) {
        value.write_at_offset_le(self, offset_in_bytes);
    }

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
    #[inline(always)]
    pub unsafe fn write_bytes(&mut self, data: &[u8]) {
        copy_nonoverlapping(data.as_ptr(), self.ptr, data.len());
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

impl EndianWriterTrait for LittleEndianWriter {
    unsafe fn write_bytes(&mut self, data: &[u8]) {
        self.write_bytes(data)
    }

    unsafe fn seek(&mut self, offset: isize) {
        self.seek(offset)
    }
}

/// Blanket implementation: Automatically implement `WriteLittleEndian` for any type
/// that implements `WriteLittleEndianAtOffset` and `HasSize`.
impl<T> WriteLittleEndian for T
where
    T: WriteLittleEndianAtOffset + HasSize,
{
    #[inline(always)]
    unsafe fn write_le(self, writer: &mut LittleEndianWriter) {
        // Write at current position (offset 0)
        self.write_at_offset_le(writer, 0);
        // Advance the writer's pointer by the serialized size
        writer.seek(T::size_in_bytes() as isize);
    }
}

// Implement WriteLittleEndian for various integer types
macro_rules! impl_write_little_endian {
    ($($t:ty),*) => {
        $(
            impl WriteLittleEndianAtOffset for $t {
                #[inline(always)]
                #[allow(clippy::size_of_in_element_count)]
                unsafe fn write_at_offset_le(self, writer: &mut LittleEndianWriter, offset_in_bytes: isize) {
                    write_unaligned((writer.ptr.offset(offset_in_bytes) as *mut $t), self.to_le());
                }
            }
        )*
    };
}

impl_write_little_endian!(i8, u8, i16, u16, i32, u32, i64, u64);

// Special implementation for floating-point types
macro_rules! impl_write_little_endian_float {
    ($($t:ty),*) => {
        $(
            impl WriteLittleEndianAtOffset for $t {
                #[inline(always)]
                unsafe fn write_at_offset_le(self, writer: &mut LittleEndianWriter, offset_in_bytes: isize) {
                    copy_nonoverlapping(
                        self.to_le_bytes().as_ptr(),
                        writer.ptr.offset(offset_in_bytes),
                        size_of::<$t>()
                    );
                }
            }
        )*
    };
}

impl_write_little_endian_float!(f32, f64);

#[cfg(test)]
mod tests {
    use super::*;
    use core::f32;

    #[test]
    fn little_endian_writer_int() {
        let mut data: [u8; 8] = [0; 8];
        let mut writer = unsafe { LittleEndianWriter::new(data.as_mut_ptr()) };
        unsafe {
            writer.write(0x0807060504030201u64);
        }
        assert_eq!(data, [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]); // little-endian for 0x0807060504030201u64
    }

    #[test]
    fn little_endian_writer_at_offset_int() {
        let mut data: [u8; 12] = [0; 12];
        let mut writer = unsafe { LittleEndianWriter::new(data.as_mut_ptr()) };
        unsafe {
            writer.write_at_offset(0x08070605u32, 8);
        } // Write at offset 8
        assert_eq!(data[8..12], [0x05, 0x06, 0x07, 0x08]); // Check only offset part
    }

    #[test]
    fn little_endian_writer_float() {
        let mut data: [u8; 4] = [0; 4];
        let mut writer = unsafe { LittleEndianWriter::new(data.as_mut_ptr()) };
        unsafe {
            writer.write(f32::consts::PI);
        }
        assert_eq!(data, [0xDB, 0x0F, 0x49, 0x40]); // little-endian for 3.1415927f32
    }

    #[test]
    fn little_endian_writer_at_offset_float() {
        let mut data: [u8; 12] = [0; 12];
        let mut writer = unsafe { LittleEndianWriter::new(data.as_mut_ptr()) };
        unsafe {
            writer.write_at_offset(f32::consts::PI, 8);
        } // Write at offset 8
        assert_eq!(data[8..12], [0xDB, 0x0F, 0x49, 0x40]); // Check only offset part
    }
}
