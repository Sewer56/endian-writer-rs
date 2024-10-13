# endian-writer

[![Crates.io](https://img.shields.io/crates/v/endian-writer.svg)](https://crates.io/crates/endian-writer)
[![Docs.rs](https://docs.rs/endian-writer/badge.svg)](https://docs.rs/endian-writer)
[![CI](https://github.com/Sewer56/endian-writer/actions/workflows/rust.yml/badge.svg)](https://github.com/Sewer56/endian-writer/actions)

## About

[no_std] **endian_writer** is a Rust crate that provides utilities for reading and writing data in both 
little-endian and big-endian formats.

It offers interchangeable readers and writers through traits, allowing for flexible and efficient 
serialization and deserialization of data structures.

## Installation

Add `endian_writer` to your `Cargo.toml`:

```toml
[dependencies]
endian_writer = "0.1.0"  # Replace with the actual version
```

## Usage

### Basic Usage of `BigEndianReader` / `LittleEndianReader`

The `BigEndianReader`/`LittleEndianReader` allow you to read data from a raw byte pointer in 
a given endian.

```rust
use endian_writer::BigEndianReader;
use endian_writer::ReadBigEndian;
use core::mem::size_of;
use core::ptr::read_unaligned;

fn main() {
    let data: [u8; 8] = [0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]; // Big-endian for 0x0807060504030201u64
    let mut reader = unsafe { BigEndianReader::new(data.as_ptr()) };

    // Read a u64 value
    let value: u64 = unsafe { reader.read::<u64>() };
    assert_eq!(value, 0x0807060504030201);
    println!("Read value: {:#x}", value);
}
```

### Basic Usage of `BigEndianWriter` / `LittleEndianWriter`

The `BigEndianWriter`/`LittleEndianWriter` allows you to write data to a raw byte pointer in
a given endian.

```rust
use endian_writer::BigEndianWriter;
use endian_writer::WriteBigEndian;
use core::mem::size_of;
use core::ptr::write_unaligned;

fn main() {
    let mut data: [u8; 8] = [0; 8];
    let mut writer = unsafe { BigEndianWriter::new(data.as_mut_ptr()) };

    // Write a u64 value
    unsafe {
        writer.write(0x0807060504030201u64);
    }

    assert_eq!(data, [0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]);
    println!("Written data: {:?}", data);
}
```

### Interchangeable Readers/Writers via Traits

The Readers and Writers are interchangeable through the use of traits:

- Readers implement the `EndianReaderTrait`.
- Writers implement the `EndianWriterTrait`.

```rust
use endian_writer::{EndianReaderTrait, BigEndianReader, LittleEndianReader, ReadBigEndian, ReadLittleEndian};

fn read_value<T: EndianReaderTrait + ReadBigEndian>(reader: &mut T) -> u32 {
    unsafe { reader.read::<u32>() }
}

fn main() {
    // Using BigEndianReader
    let big_data: [u8; 4] = [0x00, 0x00, 0x00, 0x2A]; // Big-endian for 42u32
    let mut big_reader = unsafe { BigEndianReader::new(big_data.as_ptr()) };
    let big_value = read_value(&mut big_reader);
    assert_eq!(big_value, 42);

    // Using LittleEndianReader
    let little_data: [u8; 4] = [0x2A, 0x00, 0x00, 0x00]; // Little-endian for 42u32
    let mut little_reader = unsafe { LittleEndianReader::new(little_data.as_ptr()) };
    let little_value = read_value(&mut little_reader);
    assert_eq!(little_value, 42);

    println!("Big-endian read value: {}", big_value);
    println!("Little-endian read value: {}", little_value);
}
```

### Recommended Pattern for Serializing Structures

When serializing structures, it's efficient to use `write_at_offset` for writing multiple fields 
without repeatedly advancing the pointer.

This reduces the number of instructions and improves performance.
After writing all fields, you can advance the pointer once using `seek`.

```rust
use endian_writer::{LittleEndianWriter, BigEndianWriter, WriteLittleEndian, WriteBigEndian};
use endian_writer::traits::HasSize;
use core::ptr::write_unaligned;

// Define your structure
struct FileEntry {
    hash: u64,
    data: u64,
}

// Implement `HasSize` to specify the serialized size
// Note that it is the serialized size, not struct size.
impl HasSize for FileEntry {
    fn size_in_bytes() -> usize {
        16 // 8 bytes for `hash` + 8 bytes for `data`
    }
}

// Implement `WriteLittleEndianAtOffset` for `FileEntry`
impl WriteLittleEndianAtOffset for FileEntry {
    unsafe fn write_at_offset_le(self, writer: &mut LittleEndianWriter, offset_in_bytes: isize) {
        writer.write_at_offset::<u64>(self.hash, offset_in_bytes);
        writer.write_at_offset::<u64>(self.data, offset_in_bytes + 8);
    }
}

// Implement `WriteBigEndianAtOffset` for `FileEntry`
impl WriteBigEndianAtOffset for FileEntry {
    unsafe fn write_at_offset_be(self, writer: &mut BigEndianWriter, offset_in_bytes: isize) {
        writer.write_at_offset::<u64>(self.hash, offset_in_bytes);
        writer.write_at_offset::<u64>(self.data, offset_in_bytes + 8);
    }
}

fn main() {
    let entry = FileEntry {
        hash: 0x123456789ABCDEF0,
        data: 0x0FEDCBA987654321,
    };

    // Serialize using LittleEndianWriter
    let mut buffer_le: [u8; 16] = [0; 16];
    let mut writer_le = unsafe { LittleEndianWriter::new(buffer_le.as_mut_ptr()) };
    unsafe {
        writer_le.write(entry);
    }

    assert_eq!(
        buffer_le,
        [
            0xF0, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12, // hash in little-endian
            0x21, 0x43, 0x65, 0x87, 0xA9, 0xCB, 0xED, 0x0F  // data in little-endian
        ]
    );

    println!("Serialized buffer (Little Endian): {:?}", buffer_le);

    // Serialize using BigEndianWriter
    let mut buffer_be: [u8; 16] = [0; 16];
    let mut writer_be = unsafe { BigEndianWriter::new(buffer_be.as_mut_ptr()) };
    unsafe {
        writer_be.write(entry);
    }

    assert_eq!(
        buffer_be,
        [
            0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0, // hash in big-endian
            0x0F, 0xED, 0xCB, 0xA9, 0x87, 0x65, 0x43, 0x21  // data in big-endian
        ]
    );

    println!("Serialized buffer (Big Endian): {:?}", buffer_be);
}
```

## Development

For information on how to work with this codebase, see [README-DEV.MD](README-DEV.MD).