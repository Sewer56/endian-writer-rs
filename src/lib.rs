//! # Some Cool Reloaded Library
//! Here's the crate documentation.
#![cfg_attr(not(test), no_std)]

pub mod big_endian_reader;
pub mod big_endian_writer;
pub mod little_endian_reader;
pub mod little_endian_writer;
pub mod traits;

// Prelude
pub use big_endian_reader::*;
pub use big_endian_writer::*;
pub use little_endian_reader::*;
pub use little_endian_writer::*;
pub use traits::*;
