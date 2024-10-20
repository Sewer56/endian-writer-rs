use crate::EndianReaderTrait;
use core::mem::size_of;
use core::ptr::{copy_nonoverlapping, read_unaligned};
use paste::paste;

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

/// Macro to implement read methods for base types (excluding floats)
macro_rules! define_little_endian_read_methods {
    ($($type:ty),*) => {
        $(
            paste! {
                #[doc = concat!("Reads a [`", stringify!($type), "`] from the current position and advances the pointer.")]
                unsafe fn [<read_ $type>](&mut self) -> $type {
                    let value = read_unaligned(self.ptr as *const $type).to_le();
                    self.ptr = self.ptr.add(size_of::<$type>());
                    value
                }

                #[doc = concat!("Reads a [`", stringify!($type), "`] at the specified offset without advancing the pointer.")]
                ///
                /// # Parameters
                ///
                /// * `offset`: The offset in bytes from the current position.
                unsafe fn [<read_ $type _at_offset>](&mut self, offset: isize) -> $type {
                    let ptr_at_offset = self.ptr.offset(offset);
                    let value = read_unaligned(ptr_at_offset as *const $type).to_le();
                    value
                }
            }
        )*
    };
}

/// Macro to implement read methods for floating-point types
macro_rules! define_little_endian_float_read_methods {
    ($($type:ty),*) => {
        $(
            paste! {
                #[doc = concat!("Reads a [`", stringify!($type), "`] from the current position and advances the pointer.")]
                unsafe fn [<read_ $type>](&mut self) -> $type {
                    let mut bytes = [0u8; size_of::<$type>()];
                    copy_nonoverlapping(self.ptr, bytes.as_mut_ptr(), size_of::<$type>());
                    self.ptr = self.ptr.add(size_of::<$type>());
                    <$type>::from_le_bytes(bytes)
                }

                #[doc = concat!("Reads a [`", stringify!($type), "`] at the specified offset without advancing the pointer.")]
                ///
                /// # Parameters
                ///
                /// * `offset`: The offset in bytes from the current position.
                unsafe fn [<read_ $type:lower _at_offset>](&mut self, offset: isize) -> $type {
                    let ptr_at_offset = self.ptr.offset(offset);
                    let mut bytes = [0u8; size_of::<$type>()];
                    copy_nonoverlapping(ptr_at_offset, bytes.as_mut_ptr(), size_of::<$type>());
                    <$type>::from_le_bytes(bytes)
                }
            }
        )*
    };
}

impl EndianReaderTrait for LittleEndianReader {
    unsafe fn read_bytes(&mut self, data: &mut [u8]) {
        self.read_bytes(data)
    }

    unsafe fn seek(&mut self, offset: isize) {
        self.seek(offset)
    }

    define_little_endian_read_methods!(i8, u8, i16, u16, i32, u32, i64, u64);
    define_little_endian_float_read_methods!(f32, f64);
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::f32;

    #[test]
    fn little_endian_reader_int() {
        let data: [u8; 8] = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]; // little-endian for 0x0807060504030201u64
        let mut reader = unsafe { LittleEndianReader::new(data.as_ptr()) };
        let value: u64 = unsafe { reader.read_u64() };
        assert_eq!(value, 0x0807060504030201);
    }

    #[test]
    fn little_endian_reader_at_offset() {
        let data: [u8; 12] = [
            0x01, 0x02, 0x03, 0x04, // 0x04030201u32
            0xAA, 0xBB, 0xCC, 0xDD, // offset part
            0xDB, 0x0F, 0x49, 0x40, // little-endian for 3.1415927f32
        ];
        let mut reader = unsafe { LittleEndianReader::new(data.as_ptr()) };
        let value: f32 = unsafe { reader.read_f32_at_offset(8) };
        assert!((value - f32::consts::PI).abs() < f32::EPSILON);
    }

    #[test]
    fn little_endian_reader_float() {
        let data: [u8; 4] = [0xDB, 0x0F, 0x49, 0x40]; // little-endian for 3.1415927f32
        let mut reader = unsafe { LittleEndianReader::new(data.as_ptr()) };
        let value: f32 = unsafe { reader.read_f32() };
        assert!((value - f32::consts::PI).abs() < f32::EPSILON);
    }
}
