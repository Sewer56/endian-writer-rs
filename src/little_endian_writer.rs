use crate::EndianWriterTrait;
use core::mem::size_of;
use core::ptr::{copy_nonoverlapping, write_unaligned};
use paste::paste;

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

/// Macro to implement write methods for base types (excluding floats)
macro_rules! define_little_endian_write_methods {
    ($($type:ty),*) => {
        $(
            paste! {
                #[doc = concat!("Writes a [`", stringify!($type), "`] to the current position and advances the pointer.")]
                unsafe fn [<write_ $type>](&mut self, value: $type) {
                    write_unaligned(self.ptr as *mut $type, value.to_le());
                    self.ptr = self.ptr.add(size_of::<$type>());
                }

                #[doc = concat!("Writes a [`", stringify!($type), "`] at the specified offset without advancing the pointer.")]
                ///
                /// # Parameters
                ///
                /// * `value`: The value to write.
                /// * `offset`: The offset in bytes from the current position.
                unsafe fn [<write_ $type _at_offset>](&mut self, value: $type, offset: isize) {
                    let ptr_at_offset = self.ptr.offset(offset);
                    write_unaligned(ptr_at_offset as *mut $type, value.to_le());
                }
            }
        )*
    };
}

/// Macro to implement write methods for floating-point types
macro_rules! define_little_endian_float_write_methods {
    ($($type:ty),*) => {
        $(
            paste! {
                #[doc = concat!("Writes a [`", stringify!($type), "`] to the current position and advances the pointer.")]
                unsafe fn [<write_ $type>](&mut self, value: $type) {
                    let bytes = value.to_le_bytes();
                    copy_nonoverlapping(bytes.as_ptr(), self.ptr, size_of::<$type>());
                    self.ptr = self.ptr.add(size_of::<$type>());
                }

                #[doc = concat!("Writes a [`", stringify!($type), "`] at the specified offset without advancing the pointer.")]
                ///
                /// # Parameters
                ///
                /// * `value`: The value to write.
                /// * `offset`: The offset in bytes from the current position.
                unsafe fn [<write_ $type _at_offset>](&mut self, value: $type, offset: isize) {
                    let ptr_at_offset = self.ptr.offset(offset);
                    let bytes = value.to_le_bytes();
                    copy_nonoverlapping(bytes.as_ptr(), ptr_at_offset, size_of::<$type>());
                }
            }
        )*
    };
}

impl EndianWriterTrait for LittleEndianWriter {
    unsafe fn write_bytes(&mut self, data: &[u8]) {
        self.write_bytes(data)
    }

    unsafe fn seek(&mut self, offset: isize) {
        self.seek(offset)
    }

    define_little_endian_write_methods!(i8, u8, i16, u16, i32, u32, i64, u64);
    define_little_endian_float_write_methods!(f32, f64);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn little_endian_writer_int() {
        let mut data: [u8; 8] = [0; 8];
        let mut writer = unsafe { LittleEndianWriter::new(data.as_mut_ptr()) };
        unsafe {
            writer.write_u64(0x0807060504030201u64);
        }
        assert_eq!(data, [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]); // little-endian for 0x0807060504030201u64
    }

    #[test]
    fn little_endian_writer_at_offset_int() {
        let mut data: [u8; 12] = [0; 12];
        let mut writer = unsafe { LittleEndianWriter::new(data.as_mut_ptr()) };
        unsafe {
            writer.write_i32_at_offset(0x08070605i32, 8);
        } // Write at offset 8
        assert_eq!(data[8..12], [0x05, 0x06, 0x07, 0x08]); // Check only offset part
    }

    #[test]
    fn little_endian_writer_float() {
        let mut data: [u8; 4] = [0; 4];
        let mut writer = unsafe { LittleEndianWriter::new(data.as_mut_ptr()) };
        unsafe {
            writer.write_f32(core::f32::consts::PI);
        }
        assert_eq!(data, [0xDB, 0x0F, 0x49, 0x40]); // little-endian for 3.1415927f32
    }

    #[test]
    fn little_endian_writer_at_offset_float() {
        let mut data: [u8; 12] = [0; 12];
        let mut writer = unsafe { LittleEndianWriter::new(data.as_mut_ptr()) };
        unsafe {
            writer.write_f32_at_offset(core::f32::consts::PI, 8);
        } // Write at offset 8
        assert_eq!(data[8..12], [0xDB, 0x0F, 0x49, 0x40]); // Check only offset part
    }
}
