# endian-writer

[![Crates.io](https://img.shields.io/crates/v/endian-writer.svg)](https://crates.io/crates/endian-writer)
[![Docs.rs](https://docs.rs/endian-writer/badge.svg)](https://docs.rs/endian-writer)
[![CI](https://github.com/Sewer56/endian-writer-rs/actions/workflows/rust.yml/badge.svg)](https://github.com/Sewer56/endian-writer-rs/actions)

A `no_std` Rust crate for efficient reading and writing of data structures to raw pointers in a stream-like fashion, with support for both little-endian and big-endian formats.

## Quick Start

Add to your `Cargo.toml`:

```toml
[dependencies]
endian_writer = "2.2.0"
```

```rust
use endian_writer::*;

unsafe {
    // Writing
    let mut buffer: [u8; 8] = [0; 8];
    let mut writer = LittleEndianWriter::new(buffer.as_mut_ptr());
    writer.write_u64(0x0807060504030201u64);

    // Reading
    let mut reader = LittleEndianReader::new(buffer.as_ptr());
    let value: u64 = reader.read_u64();
    assert_eq!(value, 0x0807060504030201);
}
```

See the [endian-writer crate documentation](./src/endian-writer/README.MD) for detailed usage, trait-based abstractions, and advanced features.

## Developer Manual

For step-by-step development guidance, see the [Developer Manual](https://reloaded-project.github.io/reloaded-templates-rust/manual/).

## Contributing

We welcome contributions! See the [Contributing Guide](https://reloaded-project.github.io/reloaded-templates-rust/manual/#contributing) for details.

## License

Licensed under [MIT](./LICENSE).
