# Normalizer

Prepare O0-emitted LLVM IR for Lean4 translation: SSA locals, canonical CFG, canonical loops, readable names.
**Not** a performance optimization pipeline.

## Clang emit

Keep **`-O0`** semantics; allow chosen LLVM passes to run:

```text
-emit-llvm -S -O0 -Xclang -disable-O0-optnone -fno-discard-value-names -target x86_64-unknown-linux-gnu
```

## Pipeline

**Authoritative:** [`src/normalizer/pipeline.rs`](../src/normalizer/pipeline.rs) — pass names, phase grouping, and order.

Current `opt -passes=` string:

```bash
just bitc-print-pipeline
```

Per-pass one-liners live as `=>` blurbs in the `pipeline!` block in `pipeline.rs`.
Do not duplicate pass lists or phase order here.

## Excluded passes

| Pass | Reason |
|------|--------|
| `instcombine` | Too aggressive (e.g. `1+2` → `3`); obscures step-by-step structure. Use `instsimplify` instead. |
| `fix-irreducible` | Only for irreducible CFG; not expected in our input. |
| `loop-rotate` | Changes `for` shape to do/while; hurts source-aligned reading. |
| Loop unroll / vectorize / LICM / inlining | Change structure and semantics presentation, not translation prep. |

## Invariants

- **`lcssa` after `indvars`**: `indvars` may introduce φ nodes; `lcssa` closes live-out values at exits. We omit `instcombine`, so those φ are not stripped afterward.
- **Single function `simplifycfg`**: early only; loop CFG cleanup is `loop-simplifycfg`. Add a late function `simplifycfg` only if profiling shows leftover junk blocks.
- **Address-taken `alloca`**: not promoted; the translator must handle escaping stack slots (see `bitc` normalizer tests).
