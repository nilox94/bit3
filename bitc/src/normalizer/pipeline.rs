//! LLVM `opt -passes=` pipeline for Lean4-oriented IR normalization.
//!
//! Narrative context: [`../../docs/normalizer.md`](../../docs/normalizer.md).
//! **Pass names and order in the `pipeline!` block below are authoritative.**

crate::pipeline! {
    phase "Memory → SSA" {
        "sroa" => "split aggregate allocas into scalars before mem2reg",
        "simplifycfg" => "canonical function CFG (empty blocks, branch shape)",
        "break-crit-edges" => "split critical edges so phi / mem2reg behave correctly",
        "mem2reg" => "promote promotable stack slots to SSA (+ phi at merges)",
    }
    phase "Scalar cleanup" {
        "instsimplify" => "light peepholes on SSA; not instcombine",
        "dce" => "drop dead instructions/blocks exposed by instsimplify",
    }
    phase "Control shape" {
        "lowerswitch" => "switch → compare/branch trees before loop canon",
        "mergereturn" => "single function exit where possible",
    }
    phase "Loop canonical form" {
        "loop-simplify" => "preheader, single latch/backedge, dedicated exits",
        "loop-simplifycfg" => "CFG cleanup inside loop bodies",
        "indvars" => "canonical induction variables; needs loop-simplify form",
        "lcssa" => "closing phi at loop exits for values used outside",
    }
    phase "Finalize" {
        "instnamer" => "human-readable names for unnamed SSA values",
        "verify" => "IR sanity check (must be last)",
    }
}
