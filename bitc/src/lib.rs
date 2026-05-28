//! Translator library crate — IR loading and normalization for `bitc`.

mod macros;
pub mod normalizer;

pub use normalizer::NORMALIZE_PASS_PIPELINE;
