//! Load LLVM IR (`.ll` / bitcode `.bc`) and run the Lean4-prep normalization pipeline.
//!
//! Pass list and order: [`pipeline`] (`NORMALIZE_PASS_PIPELINE`).

mod pipeline;

pub use pipeline::NORMALIZE_PASS_PIPELINE;

use std::ffi::OsStr;
use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::Once;

use inkwell::OptimizationLevel;
use inkwell::context::Context;
use inkwell::memory_buffer::MemoryBuffer;
use inkwell::module::Module;
use inkwell::passes::PassBuilderOptions;
use inkwell::support::LLVMString;
use inkwell::targets::{
    CodeModel, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple,
};

/// Errors surfaced when loading LLVM input or running normalization passes.
#[derive(Debug)]
pub enum NormalizerError {
    UnsupportedPathExtension { path: PathBuf },
    Io(std::io::Error),
    LlvmParse { path: PathBuf, message: String },
    PassPipeline(String),
    Target(String),
}

impl fmt::Display for NormalizerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NormalizerError::UnsupportedPathExtension { path } => {
                write!(
                    f,
                    "unsupported file extension for LLVM input (expected .ll or .bc): {}",
                    path.display()
                )
            }
            NormalizerError::Io(e) => write!(f, "I/O error: {e}"),
            NormalizerError::LlvmParse { path, message } => {
                write!(
                    f,
                    "failed to parse LLVM IR from {}: {message}",
                    path.display()
                )
            }
            NormalizerError::PassPipeline(message) => {
                write!(f, "LLVM normalization pass pipeline failed: {message}")
            }
            NormalizerError::Target(message) => {
                write!(f, "LLVM target initialization failed: {message}")
            }
        }
    }
}

impl std::error::Error for NormalizerError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            NormalizerError::Io(e) => Some(e),
            _ => None,
        }
    }
}

impl From<std::io::Error> for NormalizerError {
    fn from(e: std::io::Error) -> Self {
        NormalizerError::Io(e)
    }
}

fn llvm_string_message(err: LLVMString) -> String {
    err.to_string()
}

fn file_extension_normalized(path: &Path) -> Option<String> {
    path.extension()
        .and_then(OsStr::to_str)
        .map(|ext| ext.to_ascii_lowercase())
}

fn parse_module<'ctx>(
    ctx: &'ctx Context,
    path: &Path,
    ext: &str,
) -> Result<Module<'ctx>, NormalizerError> {
    let path_buf = path.to_path_buf();
    match ext {
        "bc" => {
            Module::parse_bitcode_from_path(path, ctx).map_err(|e| NormalizerError::LlvmParse {
                path: path_buf,
                message: llvm_string_message(e),
            })
        }
        "ll" => {
            let buffer =
                MemoryBuffer::create_from_file(path).map_err(|e| NormalizerError::LlvmParse {
                    path: path_buf.clone(),
                    message: llvm_string_message(e),
                })?;
            ctx.create_module_from_ir(buffer)
                .map_err(|e| NormalizerError::LlvmParse {
                    path: path_buf,
                    message: llvm_string_message(e),
                })
        }
        _ => Err(NormalizerError::UnsupportedPathExtension { path: path_buf }),
    }
}

/// Registers all LLVM backends once per process (`run_passes` requires a target-aware pipeline).
static INIT_LLVM_TARGETS: Once = Once::new();

fn ensure_llvm_targets_initialized() {
    INIT_LLVM_TARGETS.call_once(|| {
        Target::initialize_all(&InitializationConfig::default());
    });
}

/// Triple used to build the `TargetMachine` for `run_passes`.
///
/// Prefer the module's `target triple` from the IR/bitcode. Hand-written fixtures often omit it;
/// LLVM then reports an empty triple, and we fall back to the host default (same as Clang's "no
/// target" behavior for many tools).
fn triple_for_pass_runner(module: &Module<'_>) -> TargetTriple {
    let from_module = module.get_triple();
    if from_module.as_str().to_bytes().is_empty() {
        TargetMachine::get_default_triple()
    } else {
        TargetMachine::normalize_triple(&from_module)
    }
}

fn target_machine_for_module(module: &Module<'_>) -> Result<TargetMachine, NormalizerError> {
    ensure_llvm_targets_initialized();
    let triple = triple_for_pass_runner(module);
    let target = Target::from_triple(&triple)
        .map_err(|e| NormalizerError::Target(llvm_string_message(e)))?;
    target
        .create_target_machine(
            &triple,
            "generic",
            "",
            OptimizationLevel::None,
            RelocMode::Default,
            CodeModel::Default,
        )
        .ok_or_else(|| {
            NormalizerError::Target(
                "could not construct TargetMachine for module triple (create_target_machine returned None)"
                    .into(),
            )
        })
}

/// Parse an `.ll` or `.bc` file into a module in `ctx`, then run [`NORMALIZE_PASS_PIPELINE`].
pub fn normalize_path<'ctx>(
    ctx: &'ctx Context,
    path: &Path,
) -> Result<Module<'ctx>, NormalizerError> {
    let ext = file_extension_normalized(path).ok_or_else(|| {
        NormalizerError::UnsupportedPathExtension {
            path: path.to_path_buf(),
        }
    })?;

    let module = parse_module(ctx, path, ext.as_str())?;

    let target_machine = target_machine_for_module(&module)?;
    module
        .run_passes(
            NORMALIZE_PASS_PIPELINE,
            &target_machine,
            PassBuilderOptions::create(),
        )
        .map_err(|e| NormalizerError::PassPipeline(llvm_string_message(e)))?;

    Ok(module)
}
