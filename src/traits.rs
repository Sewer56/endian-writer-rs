use paste::paste;

// Macro to generate write methods for base types
macro_rules! define_write_methods {
    ($($type:ty),*) => {
        $(
            paste! {
                #[doc = concat!("Writes a [`", stringify!($type), "`] to the current position and advances the pointer.")]
                /// # Safety
                ///
                /// This method is unsafe because it writes directly to memory without bounds checking.
                unsafe fn [<write_ $type>](&mut self, value: $type);

                #[doc = concat!("Writes a [`", stringify!($type), "`] at the specified offset without advancing the pointer.")]
                ///
                /// # Parameters
                ///
                /// * `value`: The value to write.
                /// * `offset`: The offset in bytes from the current position.
                /// # Safety
                ///
                /// This method is unsafe because it writes directly to memory without bounds checking.
                unsafe fn [<write_ $type _at>](&mut self, value: $type, offset: isize);
            }
        )*
    };
}

// Macro to generate read methods for base types
macro_rules! define_read_methods {
    ($($type:ty),*) => {
        $(
            paste! {
                #[doc = concat!("Reads a [`", stringify!($type), "`] from the current position and advances the pointer.")]
                /// # Safety
                ///
                /// This method is unsafe because it reads directly from memory without bounds checking.
                unsafe fn [<read_ $type>](&mut self) -> $type;

                #[doc = concat!("Reads a [`", stringify!($type), "`] at the specified offset without advancing the pointer.")]
                ///
                /// # Parameters
                ///
                /// * `offset`: The offset in bytes from the current position.
                ///
                /// # Safety
                ///
                /// This method is unsafe because it reads directly from memory without bounds checking.
                unsafe fn [<read_ $type _at>](&mut self, offset: isize) -> $type;
            }
        )*
    };
}

/// A trait for types that can be serialized using an [`EndianWriter`].
///
/// Implement this trait for any type that you want to serialize with an [`EndianWriter`].
///
/// # Example
///
/// ```rust
/// use endian_writer::{EndianWriter, LittleEndianWriter, BigEndianWriter, EndianWritable};
///
/// struct MyStruct {
///     a: u32,
///     b: u16,
/// }
///
/// impl EndianWritable for MyStruct {
///     unsafe fn write<W: EndianWriter>(&self, writer: &mut W) {
///         // Write fields at specific offsets
///         writer.write_u32_at(self.a, 0);
///         writer.write_u16_at(self.b, 4);
///         // Advance the pointer after writing all fields
///         writer.seek(6 as isize);
///     }
/// }
/// ```
pub trait EndianWritable {
    /// Serializes the object using the provided [`EndianWriter`].
    ///
    /// # Parameters
    ///
    /// * `writer`: A mutable reference to an object implementing [`EndianWriter`].
    ///
    /// # Safety
    ///
    /// This method is unsafe because it involves writing directly to memory without bounds checking.
    unsafe fn write<W: EndianWriter>(&self, writer: &mut W);
}

/// A trait for types that can be serialized at specific offsets using an [`EndianWriter`].
///
/// Implement this trait for any type that you want to serialize with an [`EndianWriter`] at a specific offset.
///
/// # Example
///
/// ```rust
/// use endian_writer::{EndianWriter, LittleEndianWriter, EndianWritableAt};
///
/// struct MyStruct {
///     a: u32,
///     b: u16,
/// }
///
/// impl EndianWritableAt for MyStruct {
///     unsafe fn write_at<W: EndianWriter>(&self, writer: &mut W, offset: isize) {
///         writer.write_u32_at(self.a, offset);
///         writer.write_u16_at(self.b, offset + 4);
///     }
/// }
/// ```
pub trait EndianWritableAt {
    /// Serializes the object using the provided [`EndianWriter`] at the specified offset.
    ///
    /// # Parameters
    ///
    /// * `writer`: A mutable reference to an object implementing [`EndianWriter`].
    /// * `offset`: The offset in bytes from the current position.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it involves writing directly to memory without bounds checking.
    unsafe fn write_at<W: EndianWriter>(&self, writer: &mut W, offset: isize);
}

/// A trait for types that can be deserialized using an [`EndianReader`].
///
/// Implement this trait for any type that you want to deserialize with an [`EndianReader`].
///
/// # Example
///
/// ```rust
/// use endian_writer::{EndianReader, LittleEndianReader, BigEndianReader, EndianReadable};
///
/// struct MyStruct {
///     a: u32,
///     b: u16,
/// }
///
/// impl EndianReadable for MyStruct {
///     unsafe fn read<R: EndianReader>(reader: &mut R) -> Self {
///         // Read fields from specific offsets
///         let a = reader.read_u32_at(0);
///         let b = reader.read_u16_at(4);
///         // Advance the pointer after reading all fields
///         reader.seek(6 as isize);
///         MyStruct { a, b }
///     }
/// }
/// ```
pub trait EndianReadable: Sized {
    /// Deserializes the object using the provided [`EndianReader`].
    ///
    /// # Parameters
    ///
    /// * `reader`: A mutable reference to an object implementing [`EndianReader`].
    ///
    /// # Returns
    ///
    /// An instance of the implementing type.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it involves reading directly from memory without bounds checking.
    unsafe fn read<R: EndianReader>(reader: &mut R) -> Self;
}

/// A trait for types that can be deserialized at specific offsets using an [`EndianReader`].
///
/// Implement this trait for any type that you want to deserialize with an [`EndianReader`] at a specific offset.
///
/// # Example
///
/// ```rust
/// use endian_writer::{EndianReader, LittleEndianReader, EndianReadableAt};
///
/// struct MyStruct {
///     a: u32,
///     b: u16,
/// }
///
/// impl EndianReadableAt for MyStruct {
///     unsafe fn read_at<R: EndianReader>(reader: &mut R, offset: isize) -> Self {
///         let a = reader.read_u32_at(offset);
///         let b = reader.read_u16_at(offset + 4);
///         Self { a, b }
///     }
/// }
/// ```
pub trait EndianReadableAt: Sized {
    /// Deserializes the object using the provided [`EndianReader`] at the specified offset.
    ///
    /// # Parameters
    ///
    /// * `reader`: A mutable reference to an object implementing [`EndianReader`].
    /// * `offset`: The offset in bytes from the current position.
    ///
    /// # Returns
    ///
    /// An instance of the implementing type.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it involves reading directly from memory without bounds checking.
    unsafe fn read_at<R: EndianReader>(reader: &mut R, offset: isize) -> Self;
}

/// A trait for endian writers to allow interchangeable usage.
///
/// # Example
///
/// ```rust
/// use endian_writer::{EndianWriter, LittleEndianWriter, BigEndianWriter, EndianWritable};
///
/// struct MyStruct {
///     a: u32,
///     b: u16,
/// }
///
/// impl EndianWritable for MyStruct {
///     unsafe fn write<W: EndianWriter>(&self, writer: &mut W) {
///         // Write fields at specific offsets
///         writer.write_u32_at(self.a, 0);
///         writer.write_u16_at(self.b, 4);
///         // Advance the pointer after writing all fields
///         writer.seek(6 as isize);
///     }
/// }
/// ```
///
/// This trait can also be used to write any type that implements [`EndianWritable`] with the
/// [`EndianWriter::write`] method.
///
/// ```ignore
/// let mut buffer = [0u8; 6];
/// let mut writer = unsafe { LittleEndianWriter::new(buffer.as_mut_ptr()) };
/// let my_struct = MyStruct { a: 0x12345678, b: 0x9ABC };
/// unsafe {
///     writer.write(&my_struct);
/// }
/// ```
pub trait EndianWriter {
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

    define_write_methods!(i8, u8, i16, u16, i32, u32, i64, u64, f32, f64);

    /// Writes a value of type `T` that implements [`EndianWritable`].
    ///
    /// # Parameters
    ///
    /// * `value`: The value to serialize and write.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it invokes `serialize`, which involves writing
    /// directly to memory without bounds checking. The caller must ensure that
    /// there's enough space to serialize the value.
    unsafe fn write<T: EndianWritable>(&mut self, value: &T)
    where
        Self: Sized,
    {
        value.write(self)
    }

    /// Writes a value of type `T` that implements [`EndianWritableAt`] at the specified offset
    /// without changing the current pointer/cursor position.
    ///
    /// # Parameters
    ///
    /// * `value`: The value to serialize and write.
    /// * `offset`: The offset in bytes from the current position where the value will be written.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it involves writing directly to memory without bounds checking.
    /// The caller must ensure that there's enough space to serialize the value at the specified offset.
    unsafe fn write_at<T: EndianWritableAt>(&mut self, value: &T, offset: isize)
    where
        Self: Sized,
    {
        value.write_at(self, offset)
    }
}

/// A trait for endian readers to allow interchangeable usage.
///
/// # Example
///
/// ```rust
/// use endian_writer::{EndianReader, LittleEndianReader, BigEndianReader, EndianReadable};
///
/// struct MyStruct {
///     a: u32,
///     b: u16,
/// }
///
/// impl EndianReadable for MyStruct {
///     unsafe fn read<R: EndianReader>(reader: &mut R) -> Self {
///         // Read fields from specific offsets
///         let a = reader.read_u32_at(0);
///         let b = reader.read_u16_at(4);
///         // Advance the pointer after reading all fields
///         reader.seek(6 as isize);
///         MyStruct { a, b }
///     }
/// }
/// ```
///
/// This trait can also be used to read any type that implements [`EndianReadable`] with the
/// [`EndianReader::read`] method.
///
/// ```ignore
/// let data: [u8; 6] = [0x78, 0x56, 0x34, 0x12, 0xBC, 0x9A];
/// let mut reader = unsafe { LittleEndianReader::new(data.as_ptr()) };
/// let my_struct: MyStruct = unsafe { reader.read() };
/// ```
pub trait EndianReader {
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

    define_read_methods!(i8, u8, i16, u16, i32, u32, i64, u64, f32, f64);

    /// Reads a value of type `T` that implements [`EndianReadable`].
    ///
    /// # Returns
    ///
    /// An instance of `T` deserialized from the current position.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it invokes `deserialize`, which involves reading
    /// directly from memory without bounds checking. The caller must ensure that
    /// there's enough data to deserialize the value.
    unsafe fn read<T: EndianReadable>(&mut self) -> T
    where
        Self: Sized,
    {
        T::read(self)
    }

    /// Reads a value of type `T` that implements [`EndianReadableAt`] from the specified offset
    /// without changing the current pointer/cursor position.
    ///
    /// # Parameters
    ///
    /// * `offset`: The offset in bytes from the current position where the value will be read.
    ///
    /// # Returns
    ///
    /// An instance of `T` deserialized from the specified offset.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it involves reading directly from memory without bounds checking.
    /// The caller must ensure that there's enough data to deserialize the value at the specified offset.
    unsafe fn read_at<T: EndianReadableAt>(&mut self, offset: isize) -> T
    where
        Self: Sized,
    {
        T::read_at(self, offset)
    }
}

/// Implementations of `EndianWritable` and `EndianReadable` for base types.
macro_rules! impl_endian_traits_for_base_types {
    ($($type:ty => $write_fn:ident, $read_fn:ident),*) => {
        $(
            paste! {
                /// Implementation of `EndianWritable` for [$type].
                impl EndianWritable for $type {
                    /// Writes the value using the provided [`EndianWriter`], advancing the cursor.
                    ///
                    /// # Safety
                    ///
                    /// This method is unsafe because it writes directly to memory without bounds checking.
                    unsafe fn write<W: EndianWriter>(&self, writer: &mut W) {
                        writer.$write_fn(*self);
                    }
                }

                /// Implementation of `EndianReadable` for [$type].
                impl EndianReadable for $type {
                    /// Reads the value using the provided [`EndianReader`], advancing the cursor.
                    ///
                    /// # Safety
                    ///
                    /// This method is unsafe because it reads directly from memory without bounds checking.
                    unsafe fn read<R: EndianReader>(reader: &mut R) -> Self {
                        reader.$read_fn()
                    }
                }

                /// Implementation of `EndianWritableAt` for [$type].
                impl EndianWritableAt for $type {
                    /// Writes the value using the provided [`EndianWriter`] at the specified offset
                    /// without advancing the cursor/pointer.
                    ///
                    /// # Parameters
                    ///
                    /// * `writer`: A mutable reference to an object implementing [`EndianWriter`].
                    /// * `offset`: The offset in bytes from the current position.
                    ///
                    /// # Safety
                    ///
                    /// This method is unsafe because it involves writing directly to memory without bounds checking.
                    unsafe fn write_at<W: EndianWriter>(&self, writer: &mut W, offset: isize) {
                        writer.[<$write_fn _at>](*self, offset);
                    }
                }

                /// Implementation of `EndianReadableAt` for [$type].
                impl EndianReadableAt for $type {
                    /// Reads the value using the provided [`EndianReader`] at the specified offset
                    /// without advancing the cursor/pointer.
                    ///
                    /// # Parameters
                    ///
                    /// * `reader`: A mutable reference to an object implementing [`EndianReader`].
                    /// * `offset`: The offset in bytes from the current position.
                    ///
                    /// # Returns
                    ///
                    /// An instance of `Self` deserialized from the specified offset.
                    ///
                    /// # Safety
                    ///
                    /// This method is unsafe because it involves reading directly from memory without bounds checking.
                    unsafe fn read_at<R: EndianReader>(reader: &mut R, offset: isize) -> Self {
                        reader.[<$read_fn _at>](offset)
                    }
                }
            }
        )*
    };
}

// Invoke the macro for each base type with corresponding write and read methods.
impl_endian_traits_for_base_types!(
    i8  => write_i8,  read_i8,
    u8  => write_u8,  read_u8,
    i16 => write_i16, read_i16,
    u16 => write_u16, read_u16,
    i32 => write_i32, read_i32,
    u32 => write_u32, read_u32,
    i64 => write_i64, read_i64,
    u64 => write_u64, read_u64,
    f32 => write_f32, read_f32,
    f64 => write_f64, read_f64
);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BigEndianReader, BigEndianWriter, LittleEndianReader, LittleEndianWriter};
    use core::f32;

    #[derive(Debug, PartialEq)]
    struct TestStruct {
        a: u32,
        b: u16,
        c: f32,
    }

    impl EndianWritable for TestStruct {
        /// Serializes `TestStruct` using the provided `EndianWriter`.
        ///
        /// # Safety
        ///
        /// The method is unsafe because it writes directly to memory without bounds checking.
        unsafe fn write<W: EndianWriter>(&self, writer: &mut W) {
            writer.write_u32(self.a);
            writer.write_u16(self.b);
            writer.write_f32(self.c);
        }
    }

    impl EndianReadable for TestStruct {
        /// Deserializes `TestStruct` using the provided `EndianReader`.
        ///
        /// # Safety
        ///
        /// The method is unsafe because it reads directly from memory without bounds checking.
        unsafe fn read<R: EndianReader>(reader: &mut R) -> Self {
            let a = reader.read_u32();
            let b = reader.read_u16();
            let c = reader.read_f32();
            TestStruct { a, b, c }
        }
    }

    #[test]
    fn little_endian_write_read() {
        let mut buffer = [0u8; 10];
        let mut writer = unsafe { LittleEndianWriter::new(buffer.as_mut_ptr()) };
        let original = TestStruct {
            a: 0x12345678,
            b: 0x9ABC,
            c: f32::consts::PI,
        };

        unsafe {
            writer.write(&original);
        }

        let mut reader = unsafe { LittleEndianReader::new(buffer.as_ptr()) };
        let deserialized: TestStruct = unsafe { reader.read() };

        assert_eq!(original, deserialized);
    }

    #[test]
    fn big_endian_write_read() {
        let mut buffer = [0u8; 10];
        let mut writer = unsafe { BigEndianWriter::new(buffer.as_mut_ptr()) };
        let original = TestStruct {
            a: 0x12345678,
            b: 0x9ABC,
            c: f32::consts::PI,
        };

        unsafe {
            writer.write(&original);
        }

        let mut reader = unsafe { BigEndianReader::new(buffer.as_ptr()) };
        let deserialized: TestStruct = unsafe { reader.read() };

        assert_eq!(original, deserialized);
    }

    #[test]
    fn partial_write_read() {
        // This test ensures that writing at an offset works correctly
        let mut buffer = [0u8; 20];
        let mut writer = unsafe { LittleEndianWriter::new(buffer.as_mut_ptr()) };
        let original = TestStruct {
            a: 0xDEADBEEF,
            b: 0xBEEF,
            c: f32::consts::E,
        };

        unsafe {
            writer.seek(10);
            writer.write(&original);
        }

        let mut reader = unsafe { LittleEndianReader::new(buffer.as_ptr().add(10)) };
        let deserialized: TestStruct = unsafe { reader.read() };

        assert_eq!(original, deserialized);
    }
}
