#![doc = include_str!("../README.MD")]
#![cfg_attr(not(test), no_std)]
#![allow(clippy::size_of_in_element_count)]
pub mod alignment;
pub mod big_endian_reader;
pub mod big_endian_writer;
pub mod little_endian_reader;
pub mod little_endian_writer;
pub mod traits;
pub mod unroll_intrinsics;

// Prelude
pub use alignment::*;
pub use big_endian_reader::*;
pub use big_endian_writer::*;
pub use little_endian_reader::*;
pub use little_endian_writer::*;
pub use traits::*;
pub use unroll_intrinsics::*;
