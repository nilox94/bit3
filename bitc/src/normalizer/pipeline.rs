//! LLVM `opt -passes=` pipeline for Lean4-oriented IR normalization.
//!
//! Narrative context: [`../../docs/normalizer.md`](../../docs/normalizer.md).
//! **Pass names and order here are authoritative.**

use crate::macros::str_join;

macro_rules! passes { ($($args:expr),+ $(,)?) => { str_join!(",", $($args),+) }; }

// Phase 1: memory → SSA (function)
const PHASE_1_MEMORY_TO_SSA: &str = passes!(
    "sroa",             // split aggregate allocas into scalars before mem2reg
    "simplifycfg",      // canonical function CFG (empty blocks, branch shape)
    "break-crit-edges", // split critical edges so phi / mem2reg behave correctly
    "mem2reg",          // promote promotable stack slots to SSA (+ phi at merges)
);

// Phase 2: light scalar cleanup (function)
const PHASE_2_SCALAR_CLEANUP: &str = passes!(
    "instsimplify", // light peepholes on SSA; not instcombine
    "dce",          // drop dead instructions/blocks exposed by instsimplify
);

// Phase 3: function-level control shape (function)
const PHASE_3_CONTROL_SHAPE: &str = passes!(
    "lowerswitch", // switch → compare/branch trees before loop canon
    "mergereturn", // single function exit where possible
);

// Phase 4: loop canonical form (loop-aware function passes)
const PHASE_4_LOOP_CANON: &str = passes!(
    "loop-simplify",    // preheader, single latch/backedge, dedicated exits
    "loop-simplifycfg", // CFG cleanup inside loop bodies
    "indvars",          // canonical induction variables; needs loop-simplify form
    "lcssa",            // closing phi at loop exits for values used outside
);

// Phase 5: readability and verification
const PHASE_5_FINALIZE: &str = passes!(
    "instnamer", // human-readable names for unnamed SSA values
    "verify",    // IR sanity check (must be last)
);

/// Comma-separated pipeline for [`super::normalize_path`].
pub const NORMALIZE_PASS_PIPELINE: &str = passes!(
    PHASE_1_MEMORY_TO_SSA,
    PHASE_2_SCALAR_CLEANUP,
    PHASE_3_CONTROL_SHAPE,
    PHASE_4_LOOP_CANON,
    PHASE_5_FINALIZE,
);
