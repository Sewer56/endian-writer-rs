# endian-writer

[![Crates.io](https://img.shields.io/crates/v/endian-writer.svg)](https://crates.io/crates/endian-writer)
[![Docs.rs](https://docs.rs/endian-writer/badge.svg)](https://docs.rs/endian-writer)
[![CI](https://github.com/Sewer56/endian-writer-rs/actions/workflows/rust.yml/badge.svg)](https://github.com/Sewer56/endian-writer-rs/actions)

## About

[no_std] **endian_writer** is a Rust crate that provides utilities for reading and writing data in both 
little-endian and big-endian formats.

It offers interchangeable readers and writers through traits, allowing for flexible and efficient 
serialization and deserialization of data structures.

## Installation

Add `endian_writer` to your `Cargo.toml`:

```toml
[dependencies]
endian_writer = "2.2.0"  # Replace with the actual version
```

## Usage

### Basic Usage of `BigEndianReader` / `LittleEndianReader`

The `BigEndianReader` and `LittleEndianReader` allow you to read data from a raw byte pointer in 
a specified endian format.

```rust
use endian_writer::*;
use core::mem::size_of;

unsafe fn example_reader() {
    // Example with BigEndianReader
    let big_data: [u8; 8] = [0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]; // Big-endian for 0x0807060504030201u64
    let mut big_reader = BigEndianReader::new(big_data.as_ptr());

    // Read a u64 value
    let big_value: u64 = big_reader.read_u64();
    assert_eq!(big_value, 0x0807060504030201);
    println!("Big-endian read value: {:#x}", big_value);

    // Example with LittleEndianReader
    let little_data: [u8; 8] = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]; // Little-endian for 0x0807060504030201u64
    let mut little_reader = LittleEndianReader::new(little_data.as_ptr());

    // Read a u64 value
    let little_value: u64 = little_reader.read_u64();
    assert_eq!(little_value, 0x0807060504030201);
    println!("Little-endian read value: {:#x}", little_value);
}
```

### Basic Usage of `BigEndianWriter` / `LittleEndianWriter`

The `BigEndianWriter` and `LittleEndianWriter` allow you to write data to a raw byte pointer in
a specified endian format.

```rust
use endian_writer::*;
use core::mem::size_of;

unsafe fn example_writer() {
    // Example with BigEndianWriter
    let mut big_data: [u8; 8] = [0; 8];
    let mut big_writer = BigEndianWriter::new(big_data.as_mut_ptr());

    // Write a u64 value
    big_writer.write_u64(0x0807060504030201u64);

    assert_eq!(big_data, [0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]); // Big-endian for 0x0807060504030201u64
    println!("Big-endian written data: {:?}", big_data);

    // Example with LittleEndianWriter
    let mut little_data: [u8; 8] = [0; 8];
    let mut little_writer = LittleEndianWriter::new(little_data.as_mut_ptr());

    // Write a u64 value
    little_writer.write_u64(0x0807060504030201u64);

    assert_eq!(little_data, [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]); // Little-endian for 0x0807060504030201u64
    println!("Little-endian written data: {:?}", little_data);
}
```

### Interchangeable Readers/Writers via Traits

Readers and writers are interchangeable through the use of traits:

- Readers implement the `EndianReader` trait.
- Writers implement the `EndianWriter` trait.
- Types that can be written/read implement `EndianWritableAt` and `EndianReadableAt`, respectively, along with `HasSize`.
    - This provides the `write`, `write_at`, `read`, `read_at` function, along with future extension methods.

This allows you to write generic functions that can operate on any endian-specific reader or writer.

```rust
use endian_writer::*;

struct FileEntry {
    hash: u64,
    data: u64,
}

/// Allows you to serialize with either LittleEndianWriter or BigEndianWriter
impl EndianWritableAt for FileEntry {
    unsafe fn write_at<W: EndianWriter>(&self, writer: &mut W, offset: isize) {
        writer.write_u64_at(self.hash, offset);
        writer.write_u64_at(self.data, offset + 8);
    }
}

impl HasSize for FileEntry {
    const SIZE: usize = 16;
}

/// Allows you to deserialize with either LittleEndianReader or BigEndianReader
impl EndianReadableAt for FileEntry {
    unsafe fn read_at<R: EndianReader>(reader: &mut R, offset: isize) -> Self {
        let hash = reader.read_u64_at(offset);
        let data = reader.read_u64_at(offset + 8);
        FileEntry { hash, data }
    }
}

unsafe fn example_serialize_deserialize() {
    let entry = FileEntry {
        hash: 0x123456789ABCDEF0,
        data: 0x0FEDCBA987654321,
    };

    // Write using LittleEndianWriter
    let mut buffer_le: [u8; 16] = [0; 16];
    let mut writer_le = LittleEndianWriter::new(buffer_le.as_mut_ptr());
    writer_le.write(&entry);

    assert_eq!(
        buffer_le,
        [
            0xF0, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12, // hash in little-endian
            0x21, 0x43, 0x65, 0x87, 0xA9, 0xCB, 0xED, 0x0F  // data in little-endian
        ]
    );
    println!("Written buffer (Little Endian): {:?}", buffer_le);

    // Write using BigEndianWriter
    let mut buffer_be: [u8; 16] = [0; 16];
    let mut writer_be = BigEndianWriter::new(buffer_be.as_mut_ptr());
    writer_be.write(&entry);

    assert_eq!(
        buffer_be,
        [
            0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0, // hash in big-endian
            0x0F, 0xED, 0xCB, 0xA9, 0x87, 0x65, 0x43, 0x21  // data in big-endian
        ]
    );
    println!("Written buffer (Big Endian): {:?}", buffer_be);

    // Read using LittleEndianReader
    let mut reader_le = LittleEndianReader::new(buffer_le.as_ptr());
    let read_le: FileEntry = reader_le.read();
    assert_eq!(read_le.hash, entry.hash);
    assert_eq!(read_le.data, entry.data);
    println!(
        "Read entry (Little Endian): hash={:#x}, data={:#x}",
        read_le.hash, read_le.data
    );

    // Read using BigEndianReader
    let mut reader_be = BigEndianReader::new(buffer_be.as_ptr());
    let read_be: FileEntry = reader_be.read();
    assert_eq!(read_be.hash, entry.hash);
    assert_eq!(read_be.data, entry.data);
    println!(
        "Read entry (Big Endian): hash={:#x}, data={:#x}",
        read_be.hash, read_be.data
    );
}
```

#### Automatically Deriving The Traits

The following piece of Rust code.

```rust ignore
use endian_writer_derive::EndianWritable;

#[derive(EndianWritable)]
#[repr(C)]
struct MyStruct {
    a: u32,
    b: u16,
    c: u8,
}
```

Will automatically derive the traits [EndianWritableAt], [EndianReadableAt],
and [HasSize] provided all children of the struct also implement these traits.

For more details and caveats, see the [endian-writer-derive] crate.

#### Performance Note

As seen in the code above, it's more efficient to use multiple `write_at` or `read_at`
methods which don't advance the read pointer. When all fields are read, use a `seek` to advance the pointer.

This approach makes it an easier job for the compiler to optimize the code, and is also faster in
debug builds.

### Extensions: Reading Slices of Structs

You can use `write_entries` and `read_entries` for efficient batch operations.

```rust
use endian_writer::*;

#[derive(Debug, PartialEq, Copy, Clone)]
struct FileEntry {
    hash: u64,
    data: u64,
}

impl EndianWritableAt for FileEntry {
    unsafe fn write_at<W: EndianWriter>(&self, writer: &mut W, offset: isize) {
        writer.write_u64_at(self.hash, offset);
        writer.write_u64_at(self.data, offset + 8);
    }
}

impl EndianReadableAt for FileEntry {
    unsafe fn read_at<R: EndianReader>(reader: &mut R, offset: isize) -> Self {
        let hash = reader.read_u64_at(offset);
        let data = reader.read_u64_at(offset + 8);
        FileEntry { hash, data }
    }
}

impl HasSize for FileEntry {
    const SIZE: usize = 16;
}

unsafe {
    let entries = [
        FileEntry { hash: 0x123456789ABCDEF0, data: 0x0FEDCBA987654321 },
        FileEntry { hash: 0x0, data: 0x1 },
    ];

    // Write a slice of 2 entries.
    let mut buffer = [0u8; 32];
    let mut writer = LittleEndianWriter::new(buffer.as_mut_ptr());
    writer.write_entries(&entries);

    // Read a slice of 2 entries.
    let mut reader = LittleEndianReader::new(buffer.as_ptr());
    let mut read_entries = [FileEntry { hash: 0, data: 0 }; 2];
    reader.read_entries(&mut read_entries);
}
```

You can also convert to/from as part of the write step, for example, write `FileEntryB` as `FileEntry`.
And read `FileEntry` as `FileEntryB`.

```rust
use endian_writer::*;

// The entry represented in the bytes
#[derive(Debug, PartialEq, Copy, Clone)]
struct FileEntry {
    hash: u64,
    data: u64,
}

// The entry represented in the code
#[derive(Debug, PartialEq, Copy, Clone)]
struct FileEntryB {
    hash: u64,
    data: u64,
}

// To FileEntry for writing.
impl From<FileEntryB> for FileEntry {
    fn from(source: FileEntryB) -> Self {
        FileEntry {
            hash: source.hash,
            data: source.data,
        }
    }
}

// To FileEntryB for reading.
impl From<FileEntry> for FileEntryB {
    fn from(source: FileEntry) -> Self {
        FileEntryB {
            hash: source.hash,
            data: source.data,
        }
    }
}

unsafe {
    let sources = vec![
        FileEntryB { hash: 0x123456789ABCDEF0, data: 0x0FEDCBA987654321 },
        FileEntryB { hash: 0x0, data: 0x1 },
    ];

    // Write 2 FileEntryB as FileEntry
    let mut buffer = [0u8; 32];
    let mut writer = LittleEndianWriter::new(buffer.as_mut_ptr());
    writer.write_entries_into::<FileEntry, FileEntryB>(&sources);

    // Read 2 FileEntry as FileEntryB
    let mut reader = LittleEndianReader::new(buffer.as_ptr());
    let mut read_entries = vec![FileEntryB { hash: 0, data: 0 }; 2];
    reader.read_entries_into::<FileEntryB, FileEntry>(&mut read_entries);
}

// Manual trait implementation, same as if you derived `EndianSerializable`
impl HasSize for FileEntry {
    const SIZE: usize = 16;
}

impl EndianWritableAt for FileEntry {
    unsafe fn write_at<W: EndianWriter>(&self, writer: &mut W, offset: isize) {
        writer.write_u64_at(self.hash, offset);
        writer.write_u64_at(self.data, offset + 8);
    }
}

impl EndianReadableAt for FileEntry {
    unsafe fn read_at<R: EndianReader>(reader: &mut R, offset: isize) -> Self {
        let hash = reader.read_u64_at(offset);
        let data = reader.read_u64_at(offset + 8);
        FileEntry { hash, data }
    }
}
```

## Development

For information on how to work with this codebase, see [README-DEV.MD](README-DEV.MD).

## License

Licensed under [MIT](./LICENSE).  

[Learn more about Reloaded's general choice of licensing for projects.][reloaded-license].

[reloaded-license]: https://reloaded-project.github.io/Reloaded.MkDocsMaterial.Themes.R2/Pages/license/
[EndianWritableAt]: https://docs.rs/endian-writer/2.1.0/endian_writer/traits/trait.EndianWritableAt.html
[EndianReadableAt]: https://docs.rs/endian-writer/2.1.0/endian_writer/traits/trait.EndianReadableAt.html
[HasSize]: https://docs.rs/endian-writer/2.1.0/endian_writer/traits/trait.HasSize.html
[endian-writer-derive]: https://github.com/Sewer56/endian-writer-derive/blob/main/README.MD#example