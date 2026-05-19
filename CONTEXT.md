# bit3 Context

The bit3 project translates LLVM IR into semantically equivalent Lean 4 code to enable formal verification of the original program using Hoare logic.

## Language

### Core Artefacts

**Translator**:
The `bitc` tool that reads low-level LLVM IR and lifts it into a high-level, monadic Lean 4 representation suitable for formal verification.
_Avoid_: Transpiler, compiler, extractor.

**Support Library**:
The `bitlib` Lean 4 package that provides the Hoare logic primitives, type system, and combinators used by the generated Lean code.
_Avoid_: Runtime, framework.

**Snapshot**:
The generated Lean 4 output file produced by the Translator. Used in tests to ensure the Translator's output does not drift unexpectedly. Never manually edited by the user.
_Avoid_: Golden file, reference file, generated artefact.

**Proof File**:
A user-owned Lean 4 file that imports a Snapshot and states theorems about the translated program. Proofs live here, not in the Snapshot.
_Avoid_: Annotation file, spec file.

### Control Flow

**Structured Control Flow Recovery**:
The process performed by `bitc` of analyzing a flat LLVM Control Flow Graph (CFG) to extract high-level structured constructs — loops and conditionals — using the Relooper/Stackifier algorithm.
_Avoid_: CFG reconstruction, decompilation.

**Irreducible Loop**:
A loop in the CFG with multiple entry points, which cannot be represented with a standard structured loop. Handled by the Translator via State-Variable Encoding.
_Avoid_: Irreducible CFG, unstructured flow.

**State-Variable Encoding**:
The fallback encoding used by the Translator when Structured Control Flow Recovery encounters an Irreducible Loop. An explicit `state : Nat` dispatch variable is introduced to simulate the multiple entry points.
_Avoid_: Goto encoding, state machine.

### Verification

**Effect Stack**:
The specific composition of monad transformers (`StateT` over `Except`) that models the capabilities of a translated function: memory mutation, early return, and undefined behavior.
_Avoid_: Monad stack, execution context.

**Hoare Triple**:
A proposition of the form `HoareM P c Q` asserting that if the Effect Stack starts in a state satisfying precondition `P`, running computation `c` produces a state satisfying postcondition `Q`.
_Avoid_: Pre/post condition pair, specification.

**Loop Invariant**:
A predicate over the Effect Stack state that holds before every iteration of a loop. The only manual annotation a user must supply when proving properties of loops.
_Avoid_: Loop annotation, inductive hypothesis.

**Trusted Computing Base (TCB)**:
The set of components whose correctness must be assumed rather than proved. In bit3 V0, the TCB is the Translator itself.
_Avoid_: Assumed components, unverified core.

---

## Example Dialogue

> **Dev:** I want to prove that this C function never overflows. Where do I put the proof?
>
> **Domain expert:** You run the Translator on the compiled IR to get a Snapshot, then write your theorem in a Proof File that imports it. The Snapshot is just the translated code — never touch it directly.
>
> **Dev:** What if the function has a loop? Do I need to annotate the C source?
>
> **Domain expert:** No. You supply a Loop Invariant inside the Proof File, as an argument to the `loopM_hoare` lemma. The `hoare` tactic handles the rest automatically.
>
> **Dev:** The IR has a weird `goto` pattern that the Translator flagged as an Irreducible Loop. What happens?
>
> **Domain expert:** The Translator uses State-Variable Encoding for that loop. Your Proof File will need a state-indexed Loop Invariant — one clause per CFG entry point — but the `stateLoopM_hoare` lemma in the Support Library guides you through it.
