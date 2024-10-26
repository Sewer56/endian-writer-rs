use crate::{EndianReadable, EndianReader, EndianWritable, EndianWriter, HasSize};

/// Extension methods for [`EndianWriter`] to provide optimized batch writing.
///
/// This trait provides a method to write multiple entries efficiently by unrolling
/// the write operations when the `aggressive_unrolling` feature is enabled.
///
/// # Example
///
/// ```rust
/// use endian_writer::{
///     EndianWriter, LittleEndianWriter, EndianWritableAt, HasSize, EndianWritable, EndianWriterExt
/// };
///
/// struct FileEntry {
///     hash: u64,
///     data: u64,
/// }
///
/// impl EndianWritableAt for FileEntry {
///     unsafe fn write_at<W: EndianWriter>(&self, writer: &mut W, offset: isize) {
///         writer.write_u64_at(self.hash, offset);
///         writer.write_u64_at(self.data, offset + 8);
///     }
/// }
///
/// impl HasSize for FileEntry {
///     const SIZE: usize = 16;
/// }
///
/// let entries = vec![
///     FileEntry { hash: 0x123456789ABCDEF0, data: 0x0FEDCBA987654321 },
///     FileEntry { hash: 0x0, data: 0x1 },
/// ];
///
/// let mut buffer = [0u8; 32];
/// let mut writer = unsafe { LittleEndianWriter::new(buffer.as_mut_ptr()) };
///
/// unsafe {
///     writer.write_entries(&entries);
/// }
///
/// // buffer now contains the serialized entries
/// ```
pub trait EndianWriterExt {
    /// Writes multiple entries using the provided [`EndianWriter`] without any manual unrolling.
    ///
    /// # Parameters
    ///
    /// * `entries`: A slice of entries to be written. Each entry must implement [`EndianWritable`] and [`HasSize`].
    ///
    /// # Safety
    ///
    /// This method is unsafe because it involves writing directly to memory without bounds checking.
    /// The caller must ensure that the writer has enough space to write all the entries.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use endian_writer::{
    ///     EndianWriter, LittleEndianWriter, EndianWritableAt, HasSize, EndianWritable, EndianWriterExt
    /// };
    ///
    /// struct FileEntry {
    ///     hash: u64,
    ///     data: u64,
    /// }
    ///
    /// impl EndianWritableAt for FileEntry {
    ///     unsafe fn write_at<W: EndianWriter>(&self, writer: &mut W, offset: isize) {
    ///         writer.write_u64_at(self.hash, offset);
    ///         writer.write_u64_at(self.data, offset + 8);
    ///     }
    /// }
    ///
    /// impl HasSize for FileEntry {
    ///     const SIZE: usize = 16;
    /// }
    ///
    /// let entries = vec![
    ///     FileEntry { hash: 0x123456789ABCDEF0, data: 0x0FEDCBA987654321 },
    ///     FileEntry { hash: 0x0, data: 0x1 },
    /// ];
    ///
    /// let mut buffer = [0u8; 32];
    /// let mut writer = unsafe { LittleEndianWriter::new(buffer.as_mut_ptr()) };
    ///
    /// unsafe {
    ///     writer.write_entries(&entries);
    /// }
    ///
    /// // buffer now contains the serialized entries
    /// ```
    unsafe fn write_entries<T: EndianWritable + HasSize>(&mut self, entries: &[T]);

    /// Writes multiple entries using the provided [`EndianWriter`] with an unroll factor of 2.
    ///
    /// # Parameters
    ///
    /// * `entries`: A slice of entries to be written. Each entry must implement [`EndianWritable`] and [`HasSize`].
    ///
    /// # Safety
    ///
    /// This method is unsafe because it involves writing directly to memory without bounds checking.
    /// The caller must ensure that the writer has enough space to write all the entries.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use endian_writer::{
    ///     EndianWriter, LittleEndianWriter, EndianWritableAt, HasSize, EndianWritable, EndianWriterExt
    /// };
    ///
    /// struct FileEntry {
    ///     hash: u64,
    ///     data: u64,
    /// }
    ///
    /// impl EndianWritableAt for FileEntry {
    ///     unsafe fn write_at<W: EndianWriter>(&self, writer: &mut W, offset: isize) {
    ///         writer.write_u64_at(self.hash, offset);
    ///         writer.write_u64_at(self.data, offset + 8);
    ///     }
    /// }
    ///
    /// impl HasSize for FileEntry {
    ///     const SIZE: usize = 16;
    /// }
    ///
    /// let entries = vec![
    ///     FileEntry { hash: 0x123456789ABCDEF0, data: 0x0FEDCBA987654321 },
    ///     FileEntry { hash: 0x0, data: 0x1 },
    /// ];
    ///
    /// let mut buffer = [0u8; 32];
    /// let mut writer = unsafe { LittleEndianWriter::new(buffer.as_mut_ptr()) };
    ///
    /// unsafe {
    ///     writer.write_entries_unroll_2(&entries);
    /// }
    ///
    /// // buffer now contains the serialized entries
    /// ```
    unsafe fn write_entries_unroll_2<T: EndianWritable + HasSize>(&mut self, entries: &[T]);

    /// Writes multiple entries using the provided [`EndianWriter`] with an unroll factor of 3.
    ///
    /// # Parameters
    ///
    /// * `entries`: A slice of entries to be written. Each entry must implement [`EndianWritable`] and [`HasSize`].
    ///
    /// # Safety
    ///
    /// This method is unsafe because it involves writing directly to memory without bounds checking.
    /// The caller must ensure that the writer has enough space to write all the entries.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use endian_writer::{
    ///     EndianWriter, LittleEndianWriter, EndianWritableAt, HasSize, EndianWritable, EndianWriterExt
    /// };
    ///
    /// struct FileEntry {
    ///     hash: u64,
    ///     data: u64,
    /// }
    ///
    /// impl EndianWritableAt for FileEntry {
    ///     unsafe fn write_at<W: EndianWriter>(&self, writer: &mut W, offset: isize) {
    ///         writer.write_u64_at(self.hash, offset);
    ///         writer.write_u64_at(self.data, offset + 8);
    ///     }
    /// }
    ///
    /// impl HasSize for FileEntry {
    ///     const SIZE: usize = 16;
    /// }
    ///
    /// let entries = vec![
    ///     FileEntry { hash: 0x123456789ABCDEF0, data: 0x0FEDCBA987654321 },
    ///     FileEntry { hash: 0x0, data: 0x1 },
    ///     FileEntry { hash: 0xFFFFFFFFFFFFFFFF, data: 0xFFFFFFFFFFFFFFFF },
    /// ];
    ///
    /// let mut buffer = [0u8; 48];
    /// let mut writer = unsafe { LittleEndianWriter::new(buffer.as_mut_ptr()) };
    ///
    /// unsafe {
    ///     writer.write_entries_unroll_3(&entries);
    /// }
    ///
    /// // buffer now contains the serialized entries
    /// ```
    unsafe fn write_entries_unroll_3<T: EndianWritable + HasSize>(&mut self, entries: &[T]);

    /// Writes multiple entries using the provided [`EndianWriter`] with an unroll factor of 4.
    ///
    /// # Parameters
    ///
    /// * `entries`: A slice of entries to be written. Each entry must implement [`EndianWritable`] and [`HasSize`].
    ///
    /// # Safety
    ///
    /// This method is unsafe because it involves writing directly to memory without bounds checking.
    /// The caller must ensure that the writer has enough space to write all the entries.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use endian_writer::{
    ///     EndianWriter, LittleEndianWriter, EndianWritableAt, HasSize, EndianWritable, EndianWriterExt
    /// };
    ///
    /// struct FileEntry {
    ///     hash: u64,
    ///     data: u64,
    /// }
    ///
    /// impl EndianWritableAt for FileEntry {
    ///     unsafe fn write_at<W: EndianWriter>(&self, writer: &mut W, offset: isize) {
    ///         writer.write_u64_at(self.hash, offset);
    ///         writer.write_u64_at(self.data, offset + 8);
    ///     }
    /// }
    ///
    /// impl HasSize for FileEntry {
    ///     const SIZE: usize = 16;
    /// }
    ///
    /// let entries = vec![
    ///     FileEntry { hash: 0x123456789ABCDEF0, data: 0x0FEDCBA987654321 },
    ///     FileEntry { hash: 0x0, data: 0x1 },
    ///     FileEntry { hash: 0xFFFFFFFFFFFFFFFF, data: 0xFFFFFFFFFFFFFFFF },
    ///     FileEntry { hash: 0xAAAAAAAAAAAAAAAA, data: 0x5555555555555555 },
    /// ];
    ///
    /// let mut buffer = [0u8; 64];
    /// let mut writer = unsafe { LittleEndianWriter::new(buffer.as_mut_ptr()) };
    ///
    /// unsafe {
    ///     writer.write_entries_unroll_4(&entries);
    /// }
    ///
    /// // buffer now contains the serialized entries
    /// ```
    unsafe fn write_entries_unroll_4<T: EndianWritable + HasSize>(&mut self, entries: &[T]);
}

impl<W: EndianWriter> EndianWriterExt for W {
    unsafe fn write_entries<T: EndianWritable + HasSize>(&mut self, entries: &[T]) {
        let ptr = entries.as_ptr();
        let end = ptr.add(entries.len());

        let mut current = ptr;
        while current < end {
            (*current).write(self);
            current = current.add(1);
        }
    }

    unsafe fn write_entries_unroll_2<T: EndianWritable + HasSize>(&mut self, entries: &[T]) {
        let len = entries.len();
        if len == 0 {
            return;
        }

        let ptr = entries.as_ptr();
        let end = ptr.add(len);
        let unrolled_end = ptr.add(len - (len % 2));
        let mut current = ptr;

        // Process two entries at a time
        while current < unrolled_end {
            (*current).write(self);
            (*current.add(1)).write(self);
            current = current.add(2);
        }

        // Handle any remaining entries
        while current < end {
            (*current).write(self);
            current = current.add(1);
        }
    }

    unsafe fn write_entries_unroll_3<T: EndianWritable + HasSize>(&mut self, entries: &[T]) {
        let len = entries.len();
        if len == 0 {
            return;
        }

        let ptr = entries.as_ptr();
        let end = ptr.add(len);
        let unrolled_end = ptr.add(len - (len % 3));
        let mut current = ptr;

        // Process three entries at a time
        while current < unrolled_end {
            (*current).write(self);
            (*current.add(1)).write(self);
            (*current.add(2)).write(self);
            current = current.add(3);
        }

        // Handle any remaining entries
        while current < end {
            (*current).write(self);
            current = current.add(1);
        }
    }

    unsafe fn write_entries_unroll_4<T: EndianWritable + HasSize>(&mut self, entries: &[T]) {
        let len = entries.len();
        if len == 0 {
            return;
        }

        let ptr = entries.as_ptr();
        let end = ptr.add(len);
        let unrolled_end = ptr.add(len - (len % 4));
        let mut current = ptr;

        // Process four entries at a time
        while current < unrolled_end {
            (*current).write(self);
            (*current.add(1)).write(self);
            (*current.add(2)).write(self);
            (*current.add(3)).write(self);
            current = current.add(4);
        }

        // Handle any remaining entries
        while current < end {
            (*current).write(self);
            current = current.add(1);
        }
    }
}

/// Extension methods for [`EndianReader`] to provide optimized batch reading.
///
/// This trait provides methods to read multiple entries efficiently by unrolling
/// the read operations when the `aggressive_unrolling` feature is enabled.
///
/// # Example
///
/// ```rust
/// use endian_writer::{
///     EndianReader, LittleEndianReader, EndianReadableAt, HasSize, EndianReadable, EndianReaderExt
/// };
///
/// #[derive(Clone)]
/// struct FileEntry {
///     hash: u64,
///     data: u64,
/// }
///
/// impl EndianReadableAt for FileEntry {
///     unsafe fn read_at<R: EndianReader>(reader: &mut R, offset: isize) -> Self {
///         let hash = reader.read_u64_at(offset);
///         let data = reader.read_u64_at(offset + 8);
///         FileEntry { hash, data }
///     }
/// }
///
/// impl HasSize for FileEntry {
///     const SIZE: usize = 16;
/// }
///
/// let buffer = [
///     0xF0, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12, // hash of first entry (Little Endian)
///     0x21, 0x43, 0x65, 0x87, 0xA9, 0xCB, 0xED, 0x0F, // data of first entry
///     0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, // hash of second entry
///     0x02, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, // data of second entry
/// ];
/// let mut reader = unsafe { LittleEndianReader::new(buffer.as_ptr()) };
/// let mut entries = vec![FileEntry { hash: 0, data: 0 }; 2];
///
/// unsafe {
///     reader.read_entries(&mut entries);
/// }
/// ```
pub trait EndianReaderExt {
    /// Reads multiple entries using the provided [`EndianReader`] without any manual unrolling.
    ///
    /// # Parameters
    ///
    /// * `entries`: A mutable slice of entries to be populated. Each entry must implement [`EndianReadable`] and [`HasSize`].
    ///
    /// # Safety
    ///
    /// This method is unsafe because it involves reading directly from memory without bounds checking.
    /// The caller must ensure that there's enough data to read all the entries.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use endian_writer::{
    ///     EndianReader, LittleEndianReader, EndianReadableAt, HasSize, EndianReadable, EndianReaderExt
    /// };
    ///
    /// #[derive(Clone)]
    /// struct FileEntry {
    ///     hash: u64,
    ///     data: u64,
    /// }
    ///
    /// impl EndianReadableAt for FileEntry {
    ///     unsafe fn read_at<R: EndianReader>(reader: &mut R, offset: isize) -> Self {
    ///         let hash = reader.read_u64_at(offset);
    ///         let data = reader.read_u64_at(offset + 8);
    ///         FileEntry { hash, data }
    ///     }
    /// }
    ///
    /// impl HasSize for FileEntry {
    ///     const SIZE: usize = 16;
    /// }
    ///
    /// let buffer = [
    ///     0xF0, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12, // hash of first entry (Little Endian)
    ///     0x21, 0x43, 0x65, 0x87, 0xA9, 0xCB, 0xED, 0x0F, // data of first entry
    ///     0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, // hash of second entry
    ///     0x02, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, // data of second entry
    /// ];
    /// let mut reader = unsafe { LittleEndianReader::new(buffer.as_ptr()) };
    /// let mut entries = vec![FileEntry { hash: 0, data: 0 }; 2];
    ///
    /// unsafe {
    ///     reader.read_entries(&mut entries);
    /// }
    /// ```
    unsafe fn read_entries<T: EndianReadable + HasSize>(&mut self, entries: &mut [T]);

    /// Reads multiple entries using the provided [`EndianReader`] with an unroll factor of 2.
    ///
    /// This method attempts to optimize the reading process by unrolling the loop
    /// and reading multiple entries in a single iteration when the `aggressive_unrolling`
    /// feature is enabled.
    ///
    /// # Parameters
    ///
    /// * `entries`: A mutable slice of entries to be populated. Each entry must implement [`EndianReadable`] and [`HasSize`].
    ///
    /// # Safety
    ///
    /// This method is unsafe because it involves reading directly from memory without bounds checking.
    /// The caller must ensure that there's enough data to read all the entries.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use endian_writer::{
    ///     EndianReader, LittleEndianReader, EndianReadableAt, HasSize, EndianReadable, EndianReaderExt
    /// };
    ///
    /// #[derive(Clone)]
    /// struct FileEntry {
    ///     hash: u64,
    ///     data: u64,
    /// }
    ///
    /// impl EndianReadableAt for FileEntry {
    ///     unsafe fn read_at<R: EndianReader>(reader: &mut R, offset: isize) -> Self {
    ///         let hash = reader.read_u64_at(offset);
    ///         let data = reader.read_u64_at(offset + 8);
    ///         FileEntry { hash, data }
    ///     }
    /// }
    ///
    /// impl HasSize for FileEntry {
    ///     const SIZE: usize = 16;
    /// }
    ///
    /// let buffer = [
    ///     0xF0, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12, // hash of first entry (Little Endian)
    ///     0x21, 0x43, 0x65, 0x87, 0xA9, 0xCB, 0xED, 0x0F, // data of first entry
    ///     0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, // hash of second entry
    ///     0x02, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, // data of second entry
    /// ];
    /// let mut reader = unsafe { LittleEndianReader::new(buffer.as_ptr()) };
    ///
    /// let mut entries = vec![FileEntry { hash: 0, data: 0 }; 2];
    ///
    /// unsafe {
    ///     reader.read_entries_unroll_2(&mut entries);
    /// }
    /// ```
    unsafe fn read_entries_unroll_2<T: EndianReadable + HasSize>(&mut self, entries: &mut [T]);

    /// Reads multiple entries using the provided [`EndianReader`] with an unroll factor of 3.
    ///
    /// # Parameters
    ///
    /// * `entries`: A mutable slice of entries to be populated. Each entry must implement [`EndianReadable`] and [`HasSize`].
    ///
    /// # Safety
    ///
    /// This method is unsafe because it involves reading directly from memory without bounds checking.
    /// The caller must ensure that there's enough data to read all the entries.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use endian_writer::{
    ///     EndianReader, LittleEndianReader, EndianReadableAt, HasSize, EndianReadable, EndianReaderExt
    /// };
    ///
    /// #[derive(Clone)]
    /// struct FileEntry {
    ///     hash: u64,
    ///     data: u64,
    /// }
    ///
    /// impl EndianReadableAt for FileEntry {
    ///     unsafe fn read_at<R: EndianReader>(reader: &mut R, offset: isize) -> Self {
    ///         let hash = reader.read_u64_at(offset);
    ///         let data = reader.read_u64_at(offset + 8);
    ///         FileEntry { hash, data }
    ///     }
    /// }
    ///
    /// impl HasSize for FileEntry {
    ///     const SIZE: usize = 16;
    /// }
    ///
    /// let buffer = [
    ///     0xF0, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12, // hash of first entry (Little Endian)
    ///     0x21, 0x43, 0x65, 0x87, 0xA9, 0xCB, 0xED, 0x0F, // data of first entry
    ///     0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, // hash of second entry
    ///     0x02, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, // data of second entry
    ///     0x04, 0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00, // hash of third entry
    ///     0x06, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, // data of third entry
    /// ];
    /// let mut reader = unsafe { LittleEndianReader::new(buffer.as_ptr()) };
    ///
    /// let mut entries = vec![
    ///     FileEntry { hash: 0, data: 0 },
    ///     FileEntry { hash: 0, data: 0 },
    ///     FileEntry { hash: 0, data: 0 },
    /// ];
    ///
    /// unsafe {
    ///     reader.read_entries_unroll_3(&mut entries);
    /// }
    /// ```
    unsafe fn read_entries_unroll_3<T: EndianReadable + HasSize>(&mut self, entries: &mut [T]);

    /// Reads multiple entries using the provided [`EndianReader`] with an unroll factor of 4.
    ///
    /// # Parameters
    ///
    /// * `entries`: A mutable slice of entries to be populated. Each entry must implement [`EndianReadable`] and [`HasSize`].
    ///
    /// # Safety
    ///
    /// This method is unsafe because it involves reading directly from memory without bounds checking.
    /// The caller must ensure that there's enough data to read all the entries.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use endian_writer::{
    ///     EndianReader, LittleEndianReader, EndianReadableAt, HasSize, EndianReadable, EndianReaderExt
    /// };
    ///
    /// #[derive(Clone)]
    /// struct FileEntry {
    ///     hash: u64,
    ///     data: u64,
    /// }
    ///
    /// impl EndianReadableAt for FileEntry {
    ///     unsafe fn read_at<R: EndianReader>(reader: &mut R, offset: isize) -> Self {
    ///         let hash = reader.read_u64_at(offset);
    ///         let data = reader.read_u64_at(offset + 8);
    ///         FileEntry { hash, data }
    ///     }
    /// }
    ///
    /// impl HasSize for FileEntry {
    ///     const SIZE: usize = 16;
    /// }
    ///
    /// let buffer = [
    ///     0xF0, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12, // hash of first entry (Little Endian)
    ///     0x21, 0x43, 0x65, 0x87, 0xA9, 0xCB, 0xED, 0x0F, // data of first entry
    ///     0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, // hash of second entry
    ///     0x02, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, // data of second entry
    ///     0x04, 0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00, // hash of third entry
    ///     0x06, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, // data of third entry
    ///     0x08, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x00, // hash of fourth entry
    ///     0x0A, 0x00, 0x00, 0x00, 0x0B, 0x00, 0x00, 0x00, // data of fourth entry
    /// ];
    /// let mut reader = unsafe { LittleEndianReader::new(buffer.as_ptr()) };
    ///
    /// let mut entries = vec![
    ///     FileEntry { hash: 0, data: 0 },
    ///     FileEntry { hash: 0, data: 0 },
    ///     FileEntry { hash: 0, data: 0 },
    ///     FileEntry { hash: 0, data: 0 },
    /// ];
    ///
    /// unsafe {
    ///     reader.read_entries_unroll_4(&mut entries);
    /// }
    /// ```
    unsafe fn read_entries_unroll_4<T: EndianReadable + HasSize>(&mut self, entries: &mut [T]);
}

impl<R: EndianReader> EndianReaderExt for R {
    unsafe fn read_entries<T: EndianReadable + HasSize>(&mut self, entries: &mut [T]) {
        for entry in entries.iter_mut() {
            *entry = T::read(self);
        }
    }

    unsafe fn read_entries_unroll_2<T: EndianReadable + HasSize>(&mut self, entries: &mut [T]) {
        let len = entries.len();
        let mut index = 0;
        let base_ptr = entries.as_mut_ptr();

        // Process two entries at a time
        while index + 2 <= len {
            let ptr = base_ptr.add(index);
            *ptr = T::read(self);
            *ptr.add(1) = T::read(self);
            index += 2;
        }

        // Handle any remaining entries
        while index < len {
            let ptr = base_ptr.add(index);
            *ptr = T::read(self);
            index += 1;
        }
    }

    unsafe fn read_entries_unroll_3<T: EndianReadable + HasSize>(&mut self, entries: &mut [T]) {
        let len = entries.len();
        if len == 0 {
            return;
        }

        let base_ptr = entries.as_mut_ptr();
        let end = base_ptr.add(len);
        let unrolled_end = base_ptr.add(len - (len % 3));
        let mut current = base_ptr;

        // Process three entries at a time
        while current < unrolled_end {
            *current = T::read(self);
            *current.add(1) = T::read(self);
            *current.add(2) = T::read(self);
            current = current.add(3);
        }

        // Handle any remaining entries
        while current < end {
            *current = T::read(self);
            current = current.add(1);
        }
    }

    unsafe fn read_entries_unroll_4<T: EndianReadable + HasSize>(&mut self, entries: &mut [T]) {
        let len = entries.len();
        if len == 0 {
            return;
        }

        let base_ptr = entries.as_mut_ptr();
        let end = base_ptr.add(len);
        let unrolled_end = base_ptr.add(len - (len % 4));
        let mut current = base_ptr;

        // Process four entries at a time
        while current < unrolled_end {
            *current = T::read(self);
            *current.add(1) = T::read(self);
            *current.add(2) = T::read(self);
            *current.add(3) = T::read(self);
            current = current.add(4);
        }

        // Handle any remaining entries
        while current < end {
            *current = T::read(self);
            current = current.add(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        EndianReadableAt, EndianReader, EndianReaderExt, EndianWritableAt, EndianWriter,
        EndianWriterExt, HasSize, LittleEndianReader, LittleEndianWriter,
    };

    struct TestEntry {
        a: u32,
        b: u16,
    }

    impl EndianWritableAt for TestEntry {
        unsafe fn write_at<W: EndianWriter>(&self, writer: &mut W, offset: isize) {
            writer.write_u32_at(self.a, offset);
            writer.write_u16_at(self.b, offset + 4);
        }
    }

    impl HasSize for TestEntry {
        const SIZE: usize = 6;
    }

    impl EndianReadableAt for TestEntry {
        unsafe fn read_at<R: EndianReader>(reader: &mut R, offset: isize) -> Self {
            let a = reader.read_u32_at(offset);
            let b = reader.read_u16_at(offset + 4);
            TestEntry { a, b }
        }
    }

    #[test]
    fn write_entries_without_unrolling() {
        let entries = vec![
            TestEntry { a: 1, b: 2 },
            TestEntry { a: 3, b: 4 },
            TestEntry { a: 5, b: 6 },
        ];

        let mut buffer = [0u8; 18]; // 3 entries * 6 bytes each
        let mut writer = unsafe { LittleEndianWriter::new(buffer.as_mut_ptr()) };

        unsafe {
            writer.write_entries(&entries);
        }

        // Verify the buffer
        assert_eq!(
            buffer,
            [
                0x01, 0x00, 0x00, 0x00, 0x02, 0x00, // first entry
                0x03, 0x00, 0x00, 0x00, 0x04, 0x00, // second entry
                0x05, 0x00, 0x00, 0x00, 0x06, 0x00, // third entry
            ]
        );
    }

    #[test]
    fn write_entries_with_unroll_2() {
        let entries = vec![
            TestEntry { a: 1, b: 2 },
            TestEntry { a: 3, b: 4 },
            TestEntry { a: 5, b: 6 },
            TestEntry { a: 7, b: 8 },
        ];

        let mut buffer = [0u8; 24]; // 4 entries * 6 bytes each
        let mut writer = unsafe { LittleEndianWriter::new(buffer.as_mut_ptr()) };

        unsafe {
            writer.write_entries_unroll_2(&entries);
        }

        // Verify the buffer
        assert_eq!(
            buffer,
            [
                0x01, 0x00, 0x00, 0x00, 0x02, 0x00, // first entry
                0x03, 0x00, 0x00, 0x00, 0x04, 0x00, // second entry
                0x05, 0x00, 0x00, 0x00, 0x06, 0x00, // third entry
                0x07, 0x00, 0x00, 0x00, 0x08, 0x00, // fourth entry
            ]
        );
    }

    #[test]
    fn write_entries_empty() {
        let entries: Vec<TestEntry> = vec![];
        let mut buffer = [0u8; 0];
        let mut writer = unsafe { LittleEndianWriter::new(buffer.as_mut_ptr()) };

        unsafe {
            writer.write_entries(&entries);
        }

        // Buffer should remain unchanged (empty)
        assert_eq!(buffer.len(), 0);
    }

    #[test]
    fn write_entries_single_entry() {
        let entries = vec![TestEntry { a: 42, b: 7 }];

        let mut buffer = [0u8; 6];
        let mut writer = unsafe { LittleEndianWriter::new(buffer.as_mut_ptr()) };

        unsafe {
            writer.write_entries(&entries);
        }

        // Verify the buffer
        assert_eq!(
            buffer,
            [
                0x2A, 0x00, 0x00, 0x00, 0x07, 0x00, // single entry
            ]
        );
    }

    #[test]
    fn write_entries_with_unroll_3() {
        let entries = vec![
            TestEntry { a: 1, b: 2 },
            TestEntry { a: 3, b: 4 },
            TestEntry { a: 5, b: 6 },
            TestEntry { a: 7, b: 8 },
            TestEntry { a: 9, b: 10 },
        ];

        let mut buffer = [0u8; 30]; // 5 entries * 6 bytes each
        let mut writer = unsafe { LittleEndianWriter::new(buffer.as_mut_ptr()) };

        unsafe {
            writer.write_entries_unroll_3(&entries);
        }

        // Verify the buffer
        assert_eq!(
            buffer,
            [
                0x01, 0x00, 0x00, 0x00, 0x02, 0x00, // first entry
                0x03, 0x00, 0x00, 0x00, 0x04, 0x00, // second entry
                0x05, 0x00, 0x00, 0x00, 0x06, 0x00, // third entry
                0x07, 0x00, 0x00, 0x00, 0x08, 0x00, // fourth entry
                0x09, 0x00, 0x00, 0x00, 0x0A, 0x00, // fifth entry
            ]
        );
    }

    #[test]
    fn write_entries_with_unroll_4() {
        let entries = vec![
            TestEntry { a: 1, b: 2 },
            TestEntry { a: 3, b: 4 },
            TestEntry { a: 5, b: 6 },
            TestEntry { a: 7, b: 8 },
            TestEntry { a: 9, b: 10 },
            TestEntry { a: 11, b: 12 },
        ];

        let mut buffer = [0u8; 36]; // 6 entries * 6 bytes each
        let mut writer = unsafe { LittleEndianWriter::new(buffer.as_mut_ptr()) };

        unsafe {
            writer.write_entries_unroll_4(&entries);
        }

        // Verify the buffer
        assert_eq!(
            buffer,
            [
                0x01, 0x00, 0x00, 0x00, 0x02, 0x00, // first entry
                0x03, 0x00, 0x00, 0x00, 0x04, 0x00, // second entry
                0x05, 0x00, 0x00, 0x00, 0x06, 0x00, // third entry
                0x07, 0x00, 0x00, 0x00, 0x08, 0x00, // fourth entry
                0x09, 0x00, 0x00, 0x00, 0x0A, 0x00, // fifth entry
                0x0B, 0x00, 0x00, 0x00, 0x0C, 0x00, // sixth entry
            ]
        );
    }

    #[test]
    fn write_entries_unroll_3_with_remainder() {
        let entries = vec![
            TestEntry { a: 1, b: 2 },
            TestEntry { a: 3, b: 4 },
            TestEntry { a: 5, b: 6 },
            TestEntry { a: 7, b: 8 },
        ];

        let mut buffer = [0u8; 24]; // 4 entries * 6 bytes each
        let mut writer = unsafe { LittleEndianWriter::new(buffer.as_mut_ptr()) };

        unsafe {
            writer.write_entries_unroll_3(&entries);
        }

        // Verify the buffer
        assert_eq!(
            buffer,
            [
                0x01, 0x00, 0x00, 0x00, 0x02, 0x00, // first entry
                0x03, 0x00, 0x00, 0x00, 0x04, 0x00, // second entry
                0x05, 0x00, 0x00, 0x00, 0x06, 0x00, // third entry
                0x07, 0x00, 0x00, 0x00, 0x08, 0x00, // fourth entry
            ]
        );
    }

    #[test]
    fn write_entries_unroll_4_with_remainder() {
        let entries = vec![
            TestEntry { a: 1, b: 2 },
            TestEntry { a: 3, b: 4 },
            TestEntry { a: 5, b: 6 },
            TestEntry { a: 7, b: 8 },
            TestEntry { a: 9, b: 10 },
        ];

        let mut buffer = [0u8; 30]; // 5 entries * 6 bytes each
        let mut writer = unsafe { LittleEndianWriter::new(buffer.as_mut_ptr()) };

        unsafe {
            writer.write_entries_unroll_4(&entries);
        }

        // Verify the buffer
        assert_eq!(
            buffer,
            [
                0x01, 0x00, 0x00, 0x00, 0x02, 0x00, // first entry
                0x03, 0x00, 0x00, 0x00, 0x04, 0x00, // second entry
                0x05, 0x00, 0x00, 0x00, 0x06, 0x00, // third entry
                0x07, 0x00, 0x00, 0x00, 0x08, 0x00, // fourth entry
                0x09, 0x00, 0x00, 0x00, 0x0A, 0x00, // fifth entry
            ]
        );
    }

    #[test]
    fn read_entries_without_unrolling() {
        let buffer = [
            0x01, 0x00, 0x00, 0x00, 0x02, 0x00, // first entry
            0x03, 0x00, 0x00, 0x00, 0x04, 0x00, // second entry
            0x05, 0x00, 0x00, 0x00, 0x06, 0x00, // third entry
        ];
        let mut reader = unsafe { LittleEndianReader::new(buffer.as_ptr()) };

        let mut entries = vec![
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
        ];

        unsafe {
            reader.read_entries(&mut entries);
        }

        assert_eq!(entries[0].a, 1);
        assert_eq!(entries[0].b, 2);
        assert_eq!(entries[1].a, 3);
        assert_eq!(entries[1].b, 4);
        assert_eq!(entries[2].a, 5);
        assert_eq!(entries[2].b, 6);
    }

    #[test]
    fn read_entries_with_unroll_2() {
        let buffer = [
            0x01, 0x00, 0x00, 0x00, 0x02, 0x00, // first entry
            0x03, 0x00, 0x00, 0x00, 0x04, 0x00, // second entry
            0x05, 0x00, 0x00, 0x00, 0x06, 0x00, // third entry
            0x07, 0x00, 0x00, 0x00, 0x08, 0x00, // fourth entry
        ];
        let mut reader = unsafe { LittleEndianReader::new(buffer.as_ptr()) };

        let mut entries = vec![
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
        ];

        unsafe {
            reader.read_entries_unroll_2(&mut entries);
        }

        assert_eq!(entries[0].a, 1);
        assert_eq!(entries[0].b, 2);
        assert_eq!(entries[1].a, 3);
        assert_eq!(entries[1].b, 4);
        assert_eq!(entries[2].a, 5);
        assert_eq!(entries[2].b, 6);
        assert_eq!(entries[3].a, 7);
        assert_eq!(entries[3].b, 8);
    }

    #[test]
    fn read_entries_unroll_3() {
        let buffer = [
            0x01, 0x00, 0x00, 0x00, 0x02, 0x00, // first entry
            0x03, 0x00, 0x00, 0x00, 0x04, 0x00, // second entry
            0x05, 0x00, 0x00, 0x00, 0x06, 0x00, // third entry
            0x07, 0x00, 0x00, 0x00, 0x08, 0x00, // fourth entry
            0x09, 0x00, 0x00, 0x00, 0x0A, 0x00, // fifth entry
        ];
        let mut reader = unsafe { LittleEndianReader::new(buffer.as_ptr()) };

        let mut entries = vec![
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
        ];

        unsafe {
            reader.read_entries_unroll_3(&mut entries);
        }

        assert_eq!(entries[0].a, 1);
        assert_eq!(entries[0].b, 2);
        assert_eq!(entries[1].a, 3);
        assert_eq!(entries[1].b, 4);
        assert_eq!(entries[2].a, 5);
        assert_eq!(entries[2].b, 6);
        assert_eq!(entries[3].a, 7);
        assert_eq!(entries[3].b, 8);
        assert_eq!(entries[4].a, 9);
        assert_eq!(entries[4].b, 10);
    }

    #[test]
    fn read_entries_unroll_4() {
        let buffer = [
            0x01, 0x00, 0x00, 0x00, 0x02, 0x00, // first entry
            0x03, 0x00, 0x00, 0x00, 0x04, 0x00, // second entry
            0x05, 0x00, 0x00, 0x00, 0x06, 0x00, // third entry
            0x07, 0x00, 0x00, 0x00, 0x08, 0x00, // fourth entry
            0x09, 0x00, 0x00, 0x00, 0x0A, 0x00, // fifth entry
            0x0B, 0x00, 0x00, 0x00, 0x0C, 0x00, // sixth entry
        ];
        let mut reader = unsafe { LittleEndianReader::new(buffer.as_ptr()) };

        let mut entries = vec![
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
        ];

        unsafe {
            reader.read_entries_unroll_4(&mut entries);
        }

        assert_eq!(entries[0].a, 1);
        assert_eq!(entries[0].b, 2);
        assert_eq!(entries[1].a, 3);
        assert_eq!(entries[1].b, 4);
        assert_eq!(entries[2].a, 5);
        assert_eq!(entries[2].b, 6);
        assert_eq!(entries[3].a, 7);
        assert_eq!(entries[3].b, 8);
        assert_eq!(entries[4].a, 9);
        assert_eq!(entries[4].b, 10);
        assert_eq!(entries[5].a, 11);
        assert_eq!(entries[5].b, 12);
    }

    #[test]
    fn read_entries_unroll_3_with_remainder() {
        let buffer = [
            0x01, 0x00, 0x00, 0x00, 0x02, 0x00, // first entry
            0x03, 0x00, 0x00, 0x00, 0x04, 0x00, // second entry
            0x05, 0x00, 0x00, 0x00, 0x06, 0x00, // third entry
            0x07, 0x00, 0x00, 0x00, 0x08, 0x00, // fourth entry
        ];
        let mut reader = unsafe { LittleEndianReader::new(buffer.as_ptr()) };

        let mut entries = vec![
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
        ];

        unsafe {
            reader.read_entries_unroll_3(&mut entries);
        }

        assert_eq!(entries[0].a, 1);
        assert_eq!(entries[0].b, 2);
        assert_eq!(entries[1].a, 3);
        assert_eq!(entries[1].b, 4);
        assert_eq!(entries[2].a, 5);
        assert_eq!(entries[2].b, 6);
        assert_eq!(entries[3].a, 7);
        assert_eq!(entries[3].b, 8);
    }

    #[test]
    fn read_entries_unroll_4_with_remainder() {
        let buffer = [
            0x01, 0x00, 0x00, 0x00, 0x02, 0x00, // first entry
            0x03, 0x00, 0x00, 0x00, 0x04, 0x00, // second entry
            0x05, 0x00, 0x00, 0x00, 0x06, 0x00, // third entry
            0x07, 0x00, 0x00, 0x00, 0x08, 0x00, // fourth entry
            0x09, 0x00, 0x00, 0x00, 0x0A, 0x00, // fifth entry
        ];
        let mut reader = unsafe { LittleEndianReader::new(buffer.as_ptr()) };

        let mut entries = vec![
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
            TestEntry { a: 0, b: 0 },
        ];

        unsafe {
            reader.read_entries_unroll_4(&mut entries);
        }

        assert_eq!(entries[0].a, 1);
        assert_eq!(entries[0].b, 2);
        assert_eq!(entries[1].a, 3);
        assert_eq!(entries[1].b, 4);
        assert_eq!(entries[2].a, 5);
        assert_eq!(entries[2].b, 6);
        assert_eq!(entries[3].a, 7);
        assert_eq!(entries[3].b, 8);
        assert_eq!(entries[4].a, 9);
        assert_eq!(entries[4].b, 10);
    }

    #[test]
    fn read_entries_empty() {
        let buffer: [u8; 0] = [];
        let mut reader = unsafe { LittleEndianReader::new(buffer.as_ptr()) };

        let mut entries: Vec<TestEntry> = vec![];

        unsafe {
            reader.read_entries(&mut entries);
        }

        // Ensure no entries are read
        assert!(entries.is_empty());
    }

    #[test]
    fn read_entries_single_entry() {
        let buffer = [
            0x2A, 0x00, 0x00, 0x00, 0x07, 0x00, // single entry
        ];
        let mut reader = unsafe { LittleEndianReader::new(buffer.as_ptr()) };

        let mut entries = vec![TestEntry { a: 0, b: 0 }];

        unsafe {
            reader.read_entries(&mut entries);
        }

        assert_eq!(entries[0].a, 42);
        assert_eq!(entries[0].b, 7);
    }
}
