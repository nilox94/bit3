# Separate Proof Files

We decided that proofs will live in separate user-owned Lean files that import the generated Lean module, rather than being inline annotations in the original C/Rust source code.

While inline annotations (like those used in Dafny or Frama-C) offer better ergonomics by keeping code and proofs co-located, they require the Translator to parse source-level comments and weave them into the generated output. This creates a fragile coupling where re-running the Translator risks overwriting user proof stubs. By keeping proofs in separate files, the generated Lean module becomes a stable, safely re-generatable artefact.
