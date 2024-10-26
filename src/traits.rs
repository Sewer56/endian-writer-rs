use paste::paste;

// Macro to generate write methods for base types
macro_rules! define_write_methods {
    ($($type:ty => $method:ident),*) => {
        $(
            paste! {
                #[doc = concat!("Writes a [`", stringify!($type), "`] to the current position and advances the pointer.")]
                /// # Safety
                ///
                /// This method is unsafe because it writes directly to memory without bounds checking.
                unsafe fn $method(&mut self, value: $type);

                #[doc = concat!("Writes a [`", stringify!($type), "`] at the specified offset without advancing the pointer.")]
                ///
                /// # Parameters
                ///
                /// * `value`: The value to write.
                /// * `offset`: The offset in bytes from the current position.
                /// # Safety
                ///
                /// This method is unsafe because it writes directly to memory without bounds checking.
                unsafe fn [<$method _at_offset>](&mut self, value: $type, offset: isize);
            }
        )*
    };
}

// Macro to generate read methods for base types
macro_rules! define_read_methods {
    ($($type:ty => $method:ident),*) => {
        $(
            paste! {
                #[doc = concat!("Reads a [`", stringify!($type), "`] from the current position and advances the pointer.")]
                /// # Safety
                ///
                /// This method is unsafe because it reads directly from memory without bounds checking.
                unsafe fn $method(&mut self) -> $type;

                #[doc = concat!("Reads a [`", stringify!($type), "`] at the specified offset without advancing the pointer.")]
                ///
                /// # Parameters
                ///
                /// * `offset`: The offset in bytes from the current position.
                ///
                /// # Safety
                ///
                /// This method is unsafe because it reads directly from memory without bounds checking.
                unsafe fn [<$method _at_offset>](&mut self, offset: isize) -> $type;
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
/// use endian_writer::{EndianWriter, LittleEndianWriter, BigEndianWriter, EndianSerializable};
///
/// struct MyStruct {
///     a: u32,
///     b: u16,
/// }
///
/// impl EndianSerializable for MyStruct {
///     unsafe fn serialize<W: EndianWriter>(&self, writer: &mut W) {
///         // Write fields at specific offsets
///         writer.write_u32_at_offset(self.a, 0);
///         writer.write_u16_at_offset(self.b, 4);
///         // Advance the pointer after writing all fields
///         writer.seek(6 as isize);
///     }
/// }
/// ```
pub trait EndianSerializable {
    /// Serializes the object using the provided [`EndianWriter`].
    ///
    /// # Parameters
    ///
    /// * `writer`: A mutable reference to an object implementing [`EndianWriter`].
    ///
    /// # Safety
    ///
    /// This method is unsafe because it involves writing directly to memory without bounds checking.
    unsafe fn serialize<W: EndianWriter>(&self, writer: &mut W);
}

/// A trait for types that can be deserialized using an [`EndianReader`].
///
/// Implement this trait for any type that you want to deserialize with an [`EndianReader`].
///
/// # Example
///
/// ```rust
/// use endian_writer::{EndianReader, LittleEndianReader, BigEndianReader, EndianDeserializable};
///
/// struct MyStruct {
///     a: u32,
///     b: u16,
/// }
///
/// impl EndianDeserializable for MyStruct {
///     unsafe fn deserialize<R: EndianReader>(reader: &mut R) -> Self {
///         // Read fields from specific offsets
///         let a = reader.read_u32_at_offset(0);
///         let b = reader.read_u16_at_offset(4);
///         // Advance the pointer after reading all fields
///         reader.seek(6 as isize);
///         MyStruct { a, b }
///     }
/// }
/// ```
pub trait EndianDeserializable: Sized {
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
    unsafe fn deserialize<R: EndianReader>(reader: &mut R) -> Self;
}

/// A trait for endian writers to allow interchangeable usage.
///
/// # Example
///
/// ```rust
/// use endian_writer::{EndianWriter, LittleEndianWriter, BigEndianWriter, EndianSerializable};
///
/// struct MyStruct {
///     a: u32,
///     b: u16,
/// }
///
/// impl EndianSerializable for MyStruct {
///     unsafe fn serialize<W: EndianWriter>(&self, writer: &mut W) {
///         // Write fields at specific offsets
///         writer.write_u32_at_offset(self.a, 0);
///         writer.write_u16_at_offset(self.b, 4);
///         // Advance the pointer after writing all fields
///         writer.seek(6 as isize);
///     }
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

    define_write_methods!(
        i8 => write_i8,
        u8 => write_u8,
        i16 => write_i16,
        u16 => write_u16,
        i32 => write_i32,
        u32 => write_u32,
        i64 => write_i64,
        u64 => write_u64,
        f32 => write_f32,
        f64 => write_f64
    );
}

/// A trait for endian readers to allow interchangeable usage.
///
/// # Example
///
/// ```rust
/// use endian_writer::{EndianReader, LittleEndianReader, BigEndianReader, EndianDeserializable};
///
/// struct MyStruct {
///     a: u32,
///     b: u16,
/// }
///
/// impl EndianDeserializable for MyStruct {
///     unsafe fn deserialize<R: EndianReader>(reader: &mut R) -> Self {
///         // Read fields from specific offsets
///         let a = reader.read_u32_at_offset(0);
///         let b = reader.read_u16_at_offset(4);
///         // Advance the pointer after reading all fields
///         reader.seek(6 as isize);
///         MyStruct { a, b }
///     }
/// }
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

    define_read_methods!(
        i8 => read_i8,
        u8 => read_u8,
        i16 => read_i16,
        u16 => read_u16,
        i32 => read_i32,
        u32 => read_u32,
        i64 => read_i64,
        u64 => read_u64,
        f32 => read_f32,
        f64 => read_f64
    );
}

/// Implementations of `EndianSerializable` and `EndianDeserializable` for base types.
macro_rules! impl_endian_traits_for_base_types {
    ($($type:ty => $write_fn:ident, $read_fn:ident),*) => {
        $(
            paste! {
                /// Implementation of `EndianSerializable` for [$type].
                impl EndianSerializable for $type {
                    /// Serializes the value using the provided [`EndianWriter`].
                    ///
                    /// # Safety
                    ///
                    /// This method is unsafe because it writes directly to memory without bounds checking.
                    unsafe fn serialize<W: EndianWriter>(&self, writer: &mut W) {
                        writer.$write_fn(*self);
                    }
                }

                /// Implementation of `EndianDeserializable` for [$type].
                impl EndianDeserializable for $type {
                    /// Deserializes the value using the provided [`EndianReader`].
                    ///
                    /// # Safety
                    ///
                    /// This method is unsafe because it reads directly from memory without bounds checking.
                    unsafe fn deserialize<R: EndianReader>(reader: &mut R) -> Self {
                        reader.$read_fn()
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
