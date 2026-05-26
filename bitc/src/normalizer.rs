//! Load LLVM IR (.ll / bitcode `.bc`) and apply the canonical normalization passes for later translation stages.
//!
//! Runs **SROA** then **mem2reg** on the parsed module (`sroa,mem2reg` pass pipeline).

use std::ffi::OsStr;
use std::fmt;
use std::path::{Path, PathBuf};

use inkwell::OptimizationLevel;
use inkwell::context::Context;
use inkwell::memory_buffer::MemoryBuffer;
use inkwell::module::Module;
use inkwell::passes::PassBuilderOptions;
use inkwell::support::LLVMString;
use inkwell::targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine};

/// Pass pipeline applied by [`normalize_path`]; SROA before mem2reg as required for translation.
pub const NORMALIZE_PASS_PIPELINE: &str = "sroa,mem2reg";

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

fn default_target_machine() -> Result<TargetMachine, NormalizerError> {
    Target::initialize_all(&InitializationConfig::default());
    let triple = TargetMachine::get_default_triple();
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
                "could not construct default TargetMachine (create_target_machine returned None)"
                    .into(),
            )
        })
}

/// Parse an `.ll` or `.bc` file into a module in `ctx`, then run SROA and mem2reg in that order.
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

    let target_machine = default_target_machine()?;
    module
        .run_passes(
            NORMALIZE_PASS_PIPELINE,
            &target_machine,
            PassBuilderOptions::create(),
        )
        .map_err(|e| NormalizerError::PassPipeline(llvm_string_message(e)))?;

    Ok(module)
}

#[cfg(test)]
mod tests {
    use super::*;
    use inkwell::values::{FunctionValue, InstructionOpcode};
    use std::fs;

    fn count_instructions_with_opcode(fn_val: FunctionValue, op: InstructionOpcode) -> usize {
        let mut n = 0;
        for bb in fn_val.get_basic_blocks() {
            let mut current = bb.get_first_instruction();
            while let Some(inst) = current {
                if inst.get_opcode() == op {
                    n += 1;
                }
                current = inst.get_next_instruction();
            }
        }
        n
    }

    fn count_opcode_in_function(
        module: &Module<'_>,
        fn_name: &str,
        op: InstructionOpcode,
    ) -> usize {
        let Some(fn_val) = module.get_function(fn_name) else {
            return 0;
        };
        count_instructions_with_opcode(fn_val, op)
    }
    const SIMPLE_PROMOTABLE_LL: &str = r#"define i32 @promotable() {
entry:
  %x = alloca i32, align 4
  store i32 42, ptr %x, align 4
  %v = load i32, ptr %x, align 4
  ret i32 %v
}

declare void @capture(ptr)

define void @not_fully_promotable() {
entry:
  %x = alloca i32, align 4
  store i32 1, ptr %x, align 4
  call void @capture(ptr %x)
  %v = load i32, ptr %x, align 4
  ret void
}
"#;

    fn normalize_ll_temp_source(ir: &str) -> (tempfile::TempDir, PathBuf) {
        let dir = tempfile::TempDir::new().unwrap();
        let path = dir.path().join("input.ll");
        fs::write(&path, ir).unwrap();
        (dir, path)
    }

    fn write_bitcode_fixture(ctx: &Context, ir: &str, bc_path: &Path) {
        let mut raw = ir.as_bytes().to_vec();
        raw.push(0);
        let buf = MemoryBuffer::create_from_memory_range_copy(raw.as_slice(), "fixture");
        let module = ctx
            .create_module_from_ir(buf)
            .expect("fixture IR must parse");
        assert!(
            module.write_bitcode_to_path(bc_path),
            "write_bitcode_to_path returned false"
        );
    }

    #[test]
    fn rejects_unsupported_extensions() {
        let dir = tempfile::TempDir::new().unwrap();
        let path = dir.path().join("foo.obj");
        fs::write(&path, b"junk").unwrap();
        let ctx = Context::create();
        match normalize_path(&ctx, &path) {
            Err(NormalizerError::UnsupportedPathExtension { .. }) => {}
            other => panic!("expected UnsupportedPathExtension, got {other:?}"),
        }
    }

    #[test]
    fn scalar_local_ll_and_bc_has_no_residual_alloca_on_promotable() {
        let ctx = Context::create();

        let (_dir, ll_path) = normalize_ll_temp_source(SIMPLE_PROMOTABLE_LL);
        let m_ll = normalize_path(&ctx, &ll_path).expect("normalize .ll");
        assert_eq!(
            count_opcode_in_function(&m_ll, "promotable", InstructionOpcode::Alloca),
            0,
            "promotable locals should eliminate scalar alloca after mem2reg"
        );

        let dir_bc = tempfile::TempDir::new().unwrap();
        let bc_path = dir_bc.path().join("m.bc");
        write_bitcode_fixture(&ctx, SIMPLE_PROMOTABLE_LL, &bc_path);
        let m_bc = normalize_path(&ctx, &bc_path).expect("normalize .bc");
        assert_eq!(
            count_opcode_in_function(&m_bc, "promotable", InstructionOpcode::Alloca),
            0
        );
    }

    #[test]
    fn address_taken_alloca_survives_normalization_and_keeps_residual_memory_ops() {
        let ctx = Context::create();
        let (_dir, path) = normalize_ll_temp_source(SIMPLE_PROMOTABLE_LL);
        let m = normalize_path(&ctx, &path).expect("normalize");

        assert!(
            count_opcode_in_function(&m, "not_fully_promotable", InstructionOpcode::Alloca) >= 1,
            "address-taken alloca must survive mem2reg"
        );
        assert!(
            count_opcode_in_function(&m, "not_fully_promotable", InstructionOpcode::Load) >= 1
                || count_opcode_in_function(&m, "not_fully_promotable", InstructionOpcode::Store)
                    >= 1,
            "expected residual load or store for escaping alloca"
        );
    }

    #[test]
    fn accepts_uppercase_ll_extension() {
        let dir = tempfile::TempDir::new().unwrap();
        let path = dir.path().join("test.LL");
        fs::write(&path, SIMPLE_PROMOTABLE_LL).unwrap();
        let ctx = Context::create();
        normalize_path(&ctx, &path).expect(".LL should be accepted");
    }

    /// Writes to a deterministic path ending in `.tmp` then renames — exercises real rename-safe loading.
    #[test]
    fn tmp_then_rename_ll() {
        let dir = tempfile::TempDir::new().unwrap();
        let final_path = dir.path().join("final.ll");
        let tmp_path = dir.path().join("final.ll.tmp");
        fs::write(&tmp_path, SIMPLE_PROMOTABLE_LL).unwrap();
        fs::rename(&tmp_path, &final_path).unwrap();
        let ctx = Context::create();
        let m = normalize_path(&ctx, &final_path).unwrap();
        assert_eq!(
            count_opcode_in_function(&m, "promotable", InstructionOpcode::Alloca),
            0
        );
    }

    #[test]
    fn nonexistent_path_reports_io_or_llvm_parse() {
        let ctx = Context::create();
        let path = Path::new("/nonexistent/bit3_normalize_test.ll");
        let err = normalize_path(&ctx, path).unwrap_err();
        match err {
            NormalizerError::Io(_) | NormalizerError::LlvmParse { .. } => {}
            other => panic!("unexpected error: {other}"),
        }
    }
}
