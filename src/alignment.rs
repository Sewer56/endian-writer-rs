/// A trait for types that support byte alignment of their internal pointers.
///
/// This trait provides functionality to check and enforce memory alignment constraints.
///
/// Alignment is always performed by moving forward in memory to the next aligned address.
/// This is particularly useful when working with binary formats that expect data to be
/// aligned to specific power-of-two boundaries.
///
/// # Safety Requirements
///
/// When using this trait to read file formats:
///
/// * The starting address must have an alignment greater than or equal to any subsequent alignment
///   that will be requested via [`ByteAlign::align_power_of_two`].
/// * For example, if the starting address is 4-byte aligned, you cannot call `align_power_of_two(8)`
///   as this would produce incorrect alignment and undefined behavior.
///     * If you need to align to 8, the starting address must be 8-byte aligned or greater.
/// * This requirement exists because alignment can only be guaranteed by moving forward from an
///   already sufficiently aligned address.
///
/// In order to ensure the starting address is sufficiently aligned, you can use a crate such as
/// [safe-allocator-api] to allocate aligned memory.
///
/// # Examples
///
/// ```rust
/// use endian_writer::*;
/// let data = vec![0u8; 64];
/// unsafe {
///     // Ensure starting address has sufficient alignment for all subsequent operations
///     assert!(data.as_ptr() as usize % 16 == 0, "Need 16-byte aligned base address");
///     let mut reader = LittleEndianReader::new(data.as_ptr());
///     
///     // Read some unaligned header data...
///     
///     // Ensure next read will be 16-byte aligned
///     if !reader.is_aligned_power_of_two(16) {
///         reader.align_power_of_two(16);
///     }
///     
///     // Now read aligned data structures...
/// }
/// ```
///
/// # Binary Format Example
///
/// In binary files, data is often aligned by adding padding bytes.
/// For instance, consider a file format where a variable-length string
/// is followed by an aligned 16-byte data structure:
///
/// ```text
/// Offset  Content
/// 0x0000  String length (1 byte)
/// 0x0001  String data ("Hello") [5 bytes]
/// 0x0006  Padding to 16-byte alignment [10 bytes]
/// 0x0010  16-byte aligned structure
/// ```
///
/// The reader can handle this by using `align_power_of_two`:
///
/// ```rust,no_run
/// use endian_writer::*;
/// let data = vec![0u8; 64];
/// unsafe {
///     // Must ensure base address has at least 16-byte alignment
///     assert!(data.as_ptr() as usize % 16 == 0, "Need 16-byte aligned base address");
///     let mut reader = LittleEndianReader::new(data.as_ptr());
///     
///     // Read string length and data...
///     
///     // Skip padding by aligning to next 16-byte boundary
///     reader.align_power_of_two(16);
///     
///     // Now at offset 0x0010, ready to read aligned structure
/// }
/// ```
///
/// [safe-allocator-api]: https://crates.io/crates/safe-allocator-api
pub trait ByteAlign {
    /// Aligns the internal pointer forward to the next memory address that satisfies
    /// the given power-of-two alignment. This is equivalent to adding padding bytes
    /// until the desired alignment is reached.
    ///
    /// # Safety
    ///
    /// This method is unsafe because:
    /// 1. It modifies the internal pointer without bounds checking
    /// 2. The caller must ensure that the starting address has an alignment greater than
    ///    or equal to `align_to`. For example, if the starting address is 4-byte aligned,
    ///    you cannot align to 8 bytes as this would produce incorrect alignment.
    /// 3. The new aligned position must be within valid memory bounds
    ///
    /// # Arguments
    ///
    /// * `align_to`: The power-of-two value to align to (e.g., 2, 4, 8, 16, 32, etc.)
    unsafe fn align_power_of_two(&mut self, align_to: usize);

    /// Checks if the internal pointer is aligned to the specified power-of-two boundary.
    ///
    /// # Arguments
    ///
    /// * `align_to`: The power-of-two alignment to check for (e.g., 2, 4, 8, 16, 32, etc.)
    ///
    /// # Returns
    ///
    /// Returns `true` if the current pointer position is aligned to the specified boundary,
    /// `false` otherwise.
    ///
    /// # Panics
    ///
    /// This function will panic in debug builds if `align_to` is not a power of 2.
    fn is_aligned_power_of_two(&self, align_to: usize) -> bool;
}

macro_rules! impl_byte_align {
    ($type:ty, $ptr_field:ident) => {
        impl ByteAlign for $type {
            #[inline]
            unsafe fn align_power_of_two(&mut self, align_to: usize) {
                debug_assert!(align_to.is_power_of_two(), "Alignment must be a power of 2");
                let mask = align_to - 1;
                let ptr = self.$ptr_field as usize;
                let aligned = (ptr + mask) & !mask;
                self.$ptr_field = aligned as *mut u8;
            }

            #[inline]
            fn is_aligned_power_of_two(&self, align_to: usize) -> bool {
                debug_assert!(align_to.is_power_of_two(), "Alignment must be a power of 2");
                let ptr = self.$ptr_field as usize;
                (ptr & (align_to - 1)) == 0
            }
        }
    };
}

// Implement for all reader/writer types
impl_byte_align!(crate::LittleEndianReader, ptr);
impl_byte_align!(crate::LittleEndianWriter, ptr);
impl_byte_align!(crate::BigEndianReader, ptr);
impl_byte_align!(crate::BigEndianWriter, ptr);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;

    #[repr(C, align(64))]
    #[derive(Copy, Clone, Debug, PartialEq)]
    struct AlignToSixtyFour([u8; 64]);

    #[test]
    fn alignment_basic() {
        // Ensure test buffer is aligned enough for all our tests
        let mut buffer = vec![AlignToSixtyFour([0; 64]); 1];
        let base_ptr = buffer.as_mut_ptr() as *mut u8;
        assert_eq!(
            base_ptr as usize % 16,
            0,
            "Test requires 16-byte aligned buffer"
        );

        unsafe {
            // Test with offset of 1 to check alignment correction
            let mut reader = LittleEndianReader::new(base_ptr.add(1));
            assert!(!reader.is_aligned_power_of_two(8));
            reader.align_power_of_two(8);
            assert!(reader.is_aligned_power_of_two(8));
            assert_eq!(reader.ptr as usize % 8, 0);
        }
    }

    #[test]
    fn alignment_checks() {
        let mut buffer = vec![AlignToSixtyFour([0; 64]); 1];
        let base_ptr = buffer.as_mut_ptr() as *mut u8;
        assert_eq!(
            base_ptr as usize % 16,
            0,
            "Test requires 16-byte aligned buffer"
        );

        unsafe {
            let mut writer = BigEndianWriter::new(base_ptr);
            assert!(writer.is_aligned_power_of_two(16));

            // Move to unaligned position
            writer.ptr = writer.ptr.add(1);
            assert!(!writer.is_aligned_power_of_two(16));
            assert!(!writer.is_aligned_power_of_two(8));
            assert!(!writer.is_aligned_power_of_two(4));
            assert!(!writer.is_aligned_power_of_two(2));
        }
    }

    #[test]
    fn alignment_successive() {
        let mut buffer = vec![AlignToSixtyFour([0; 64]); 1];
        let base_ptr = buffer.as_mut_ptr() as *mut u8;
        assert_eq!(
            base_ptr as usize % 16,
            0,
            "Test requires 16-byte aligned buffer"
        );

        unsafe {
            let mut reader = LittleEndianReader::new(base_ptr.add(1));

            // Test increasingly larger alignments
            reader.align_power_of_two(2);
            assert!(reader.is_aligned_power_of_two(2));
            let ptr2 = reader.ptr;

            reader.align_power_of_two(4);
            assert!(reader.is_aligned_power_of_two(4));
            assert!(reader.is_aligned_power_of_two(2));
            let ptr4 = reader.ptr;
            assert!(ptr4 >= ptr2);

            reader.align_power_of_two(8);
            assert!(reader.is_aligned_power_of_two(8));
            assert!(reader.is_aligned_power_of_two(4));
            assert!(reader.is_aligned_power_of_two(2));
        }
    }

    #[test]
    fn alignment_endian_equivalence() {
        let mut buffer = vec![AlignToSixtyFour([0; 64]); 1];
        let base_ptr = buffer.as_mut_ptr() as *mut u8;
        assert_eq!(
            base_ptr as usize % 16,
            0,
            "Test requires 16-byte aligned buffer"
        );

        unsafe {
            let mut le_writer = LittleEndianWriter::new(base_ptr.add(1));
            let mut be_writer = BigEndianWriter::new(base_ptr.add(1));

            le_writer.align_power_of_two(8);
            be_writer.align_power_of_two(8);

            // Alignment should be independent of endianness
            assert_eq!(le_writer.ptr, be_writer.ptr);
            assert!(le_writer.is_aligned_power_of_two(8));
            assert!(be_writer.is_aligned_power_of_two(8));
        }
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Alignment must be a power of 2")]
    fn alignment_non_power_of_two() {
        let mut buffer = vec![AlignToSixtyFour([0; 64]); 1];
        let base_ptr = buffer.as_mut_ptr() as *mut u8;

        unsafe {
            let mut reader = LittleEndianReader::new(base_ptr);
            reader.align_power_of_two(3); // Should panic in debug mode
        }
    }

    #[test]
    fn alignment_already_aligned() {
        let mut buffer = vec![AlignToSixtyFour([0; 64]); 1];
        let base_ptr = buffer.as_mut_ptr() as *mut u8;
        assert_eq!(
            base_ptr as usize % 16,
            0,
            "Test requires 16-byte aligned buffer"
        );

        unsafe {
            let mut reader = LittleEndianReader::new(base_ptr);
            let original_ptr = reader.ptr;

            // Alignment when already aligned should not change pointer
            reader.align_power_of_two(16);
            assert_eq!(reader.ptr, original_ptr);
            assert!(reader.is_aligned_power_of_two(16));
        }
    }
}
