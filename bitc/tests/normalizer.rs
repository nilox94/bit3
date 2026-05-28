use std::fs;
use std::path::{Path, PathBuf};

use bitc::NORMALIZE_PASS_PIPELINE;
use bitc::normalizer::{NormalizerError, normalize_path};
use inkwell::context::Context;
use inkwell::memory_buffer::MemoryBuffer;
use inkwell::module::Module;
use inkwell::values::{FunctionValue, InstructionOpcode};

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

fn count_opcode_in_function(module: &Module<'_>, fn_name: &str, op: InstructionOpcode) -> usize {
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

const IR_WITH_TRIPLE: &str = r#"target triple = "x86_64-pc-linux-gnu"

define i32 @promotable() {
entry:
  %x = alloca i32, align 4
  store i32 42, ptr %x, align 4
  %v = load i32, ptr %x, align 4
  ret i32 %v
}
"#;

#[test]
fn accepts_ll_with_explicit_target_triple() {
    let dir = tempfile::TempDir::new().unwrap();
    let path = dir.path().join("t.ll");
    fs::write(&path, IR_WITH_TRIPLE).unwrap();
    let ctx = Context::create();
    normalize_path(&ctx, &path).expect("normalize with module triple in IR");
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
            || count_opcode_in_function(&m, "not_fully_promotable", InstructionOpcode::Store) >= 1,
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
fn normalize_pass_pipeline_structure() {
    let passes: Vec<&str> = NORMALIZE_PASS_PIPELINE.split(',').collect();
    assert!(passes.len() > 1, "pipeline should list multiple passes");
    assert_eq!(passes.last(), Some(&"verify"), "verify must be last");
    assert!(
        !NORMALIZE_PASS_PIPELINE.contains("instcombine"),
        "instcombine is deliberately excluded"
    );

    let mem2reg = passes.iter().position(|&p| p == "mem2reg").expect("mem2reg");
    let loop_simplify = passes
        .iter()
        .position(|&p| p == "loop-simplify")
        .expect("loop-simplify");
    assert!(
        mem2reg < loop_simplify,
        "mem2reg must run before loop canonicalization"
    );

    let indvars = passes.iter().position(|&p| p == "indvars").expect("indvars");
    let lcssa = passes.iter().position(|&p| p == "lcssa").expect("lcssa");
    assert!(indvars < lcssa, "lcssa must follow indvars");
}

/// End-to-end: full pipeline on repo `examples/gcd.ll` (recursive IR, loops, calls).
#[test]
fn smoke_normalize_examples_gcd_ll() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../examples/gcd.ll");
    let ctx = Context::create();
    let module = normalize_path(&ctx, &path).expect("normalize gcd.ll");
    assert!(
        module.get_function("gcd").is_some(),
        "gcd function should survive normalization"
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
