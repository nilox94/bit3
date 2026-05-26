import Bitlib.EffectStack

namespace Bitlib

/-!
# Hoare Logic for the Effect Stack

This module defines the `HoareM` proposition and all structural lemmas for
reasoning about `EffectStack` computations. Structural rules are bundled into
a dedicated `aesop` rule set so that user proofs reduce to **Loop Invariant**
and arithmetic obligations.

## Trusted Computing Base

**Zero axioms.** `loopM` is total (fuel-indexed), so termination needs no
axiomatic justification: fuel exhaustion is observable as `UBKind.timeout`
inside the `EffectStack`, and `HoareM` is vacuously true on the error branch.

## Workflow

For straight-line code:

```lean
aesop (rule_sets := [BitcHoare])
```

For loops:

```lean
apply loopM_hoare (I := <invariant>)
intro u s hs
aesop (rule_sets := [BitcHoare])
```

`loopM_hoare` is intentionally **not** tagged with `aesop` because the
invariant `I` cannot be inferred.
-/

-- ---------------------------------------------------------------------------
-- HoareM
-- ---------------------------------------------------------------------------

section HoareM

variable {Regs Ret α β : Type}

/--
`HoareM P c Q` is a Hoare Triple for an `EffectStack` computation.
If the initial state satisfies precondition `P`, then running `c` either:
- returns normally and the resulting state satisfies postcondition `Q`, or
- throws a `ReturnOrUB` exception (early return, UB, or `timeout`), in which
  case `Q` need not hold.

This matches the partial-correctness semantics appropriate for a language
with explicit early returns and undefined behavior.
-/
def HoareM (P : FunctionState Regs → Prop)
           (c : EffectStack Regs Ret α)
           (Q : α → FunctionState Regs → Prop) : Prop :=
  ∀ s, P s →
    match c s with
    | .ok (a, s') => Q a s'
    | .error _    => True

/-- Precondition weakening (rule of consequence on the left).

    Useful when chaining `seq_hoare` (which yields a `(· = s')` precondition)
    into a `loopM_hoare` (which expects an invariant `I`): the user shows that
    the pinned state satisfies `I`, then invokes the loop lemma. -/
theorem HoareM.conseq_pre {Regs Ret α : Type}
    {P P' : FunctionState Regs → Prop}
    {c : EffectStack Regs Ret α}
    {Q : α → FunctionState Regs → Prop}
    (hP : ∀ s, P s → P' s) (h : HoareM P' c Q) : HoareM P c Q :=
  fun s hs => h s (hP s hs)

end HoareM

-- ---------------------------------------------------------------------------
-- Structural lemmas (tagged for Aesop)
-- ---------------------------------------------------------------------------

section StructuralLemmas

variable {Regs Ret α β : Type}

/-- `skip_hoare`: `pure a` satisfies any postcondition that holds for `a`
    in the current state. -/
@[aesop safe apply (rule_sets := [BitcHoare])]
theorem skip_hoare {P : FunctionState Regs → Prop}
    {Q : α → FunctionState Regs → Prop}
    {a : α}
    (h : ∀ s, P s → Q a s) :
    HoareM P (pure a : EffectStack Regs Ret α) Q := by
  intro s hs
  simp [pure, StateT.pure, Except.pure]
  exact h s hs

/-- `modify_hoare`: `modify f` satisfies `Q ()` whenever `P` implies
    `Q () (f s)`. -/
@[aesop safe apply (rule_sets := [BitcHoare])]
theorem modify_hoare {P : FunctionState Regs → Prop}
    {Q : Unit → FunctionState Regs → Prop}
    {f : FunctionState Regs → FunctionState Regs}
    (h : ∀ s, P s → Q () (f s)) :
    HoareM P (modify f : EffectStack Regs Ret Unit) Q := by
  intro s hs
  simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, Except.pure]
  exact h s hs

/-- `seq_hoare`: WLP-style sequential composition.

    The second-leg hypothesis is parameterised by the exact post-state `s'`
    produced by the first leg — no existential intermediate predicate `R` to
    invent. This is the shape `aesop` can apply mechanically. -/
@[aesop safe apply (rule_sets := [BitcHoare])]
theorem seq_hoare {P : FunctionState Regs → Prop}
    {Q : β → FunctionState Regs → Prop}
    {c : EffectStack Regs Ret α}
    {k : α → EffectStack Regs Ret β}
    (h : HoareM P c (fun a s' => HoareM (· = s') (k a) Q)) :
    HoareM P (c >>= k) Q := by
  intro s hs
  have h1 := h s hs
  show match (c >>= k) s with | .ok (b, s'') => Q b s'' | .error _ => True
  simp only [bind, StateT.bind, Except.bind]
  rcases hcs_eq : c s with ⟨e⟩ | ⟨a, s'⟩
  · simp
  · simp only [hcs_eq] at h1
    have h2 := h1 s' rfl
    rcases hk_eq : k a s' with ⟨e⟩ | ⟨b, s''⟩
    · simp [hk_eq]
    · simp only [hk_eq] at h2
      simp only [hk_eq]
      exact h2

/-- `ifM_hoare`: conditional branching. -/
@[aesop safe apply (rule_sets := [BitcHoare])]
theorem ifM_hoare {P : FunctionState Regs → Prop}
    {Q : α → FunctionState Regs → Prop}
    {cond : Bool}
    {ct cf : EffectStack Regs Ret α}
    (ht : cond = true  → HoareM P ct Q)
    (hf : cond = false → HoareM P cf Q) :
    HoareM P (if cond then ct else cf) Q := by
  cases cond
  · exact hf rfl
  · exact ht rfl

-- ---------------------------------------------------------------------------
-- Memory helpers (tagged for Aesop)
-- ---------------------------------------------------------------------------

/-- `store_hoare`: write an integer value to the residual memory map.

    Just a specialisation of `modify_hoare`, kept as a named lemma so that
    aesop can recognise the canonical store shape. -/
@[aesop safe apply (rule_sets := [BitcHoare])]
theorem store_hoare
    {P : FunctionState Regs → Prop}
    {Q : Unit → FunctionState Regs → Prop}
    {addr : Nat} {val : Int}
    (h : ∀ s, P s →
         Q () { s with memory := (addr, val) :: s.memory.filter (fun p => p.1 ≠ addr) }) :
    HoareM P
      (modify (fun s => { s with memory := (addr, val) :: s.memory.filter (fun p => p.1 ≠ addr) })
        : EffectStack Regs Ret Unit)
      Q :=
  modify_hoare h

/-- Helper: the `load` do-block reduces to a simple match on `find?`. -/
private theorem load_do_eq {Regs Ret : Type} (addr : Nat) :
    (do
      let s ← get
      match s.memory.find? (fun p => p.1 == addr) with
      | some (_, v) => pure v
      | none        => pure (0 : Int)
      : EffectStack Regs Ret Int) =
    fun s0 =>
      match s0.memory.find? (fun p => p.1 == addr) with
      | some (_, v) => .ok (v, s0)
      | none        => .ok ((0 : Int), s0) := by
  funext s0
  simp [get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind,
        pure, Except.pure, Except.bind]
  split
  · rename_i fst v heq; simp [heq, StateT.pure]; rfl
  · rename_i heq; simp [heq, StateT.pure]; rfl

/-- `load_hoare`: read an integer value from the residual memory map. -/
@[aesop safe apply (rule_sets := [BitcHoare])]
theorem load_hoare
    {P : FunctionState Regs → Prop}
    {Q : Int → FunctionState Regs → Prop}
    {addr : Nat}
    (h : ∀ s, P s →
         match s.memory.find? (fun p => p.1 == addr) with
         | some (_, v) => Q v s
         | none        => Q 0 s) :
    HoareM P
      (do
        let s ← get
        match s.memory.find? (fun p => p.1 == addr) with
        | some (_, v) => pure v
        | none        => pure 0
        : EffectStack Regs Ret Int)
      Q := by
  intro s hs
  rw [load_do_eq]
  have hh := h s hs
  rcases hm : s.memory.find? (fun p => p.1 == addr) with ⟨fst, v⟩ | _
  · simp only [hm] at hh; simp only [hm]; exact hh
  · simp only [hm] at hh; simp only [hm]; exact hh

end StructuralLemmas

-- ---------------------------------------------------------------------------
-- Loop lemma (intentionally NOT tagged with aesop)
-- ---------------------------------------------------------------------------

section LoopLemma

variable {Regs Ret α : Type}

/-- `loopM_hoare`: structured loop with a Loop Invariant.

    The user supplies `I : FunctionState Regs → Prop` that holds before every
    iteration. The body must preserve `I` on `continue` and establish `Q` on
    `break`/`return`. Termination is by structural recursion on `fuel`; fuel
    exhaustion produces `UBKind.timeout`, on which `HoareM` is vacuously true.

    Not tagged with `aesop` — the invariant cannot be inferred. The user must
    `apply loopM_hoare (I := ...)` before calling `aesop (rule_sets := [BitcHoare])`.
-/
theorem loopM_hoare
    {I : FunctionState Regs → Prop}
    {Q : α → FunctionState Regs → Prop}
    {body : Unit → EffectStack Regs Ret (LoopControl α)}
    (hbody : ∀ u, HoareM I (body u) (LoopControl.post I Q)) :
    ∀ fuel u, HoareM I (loopM fuel body u) Q := by
  intro fuel
  induction fuel with
  | zero =>
    intro u s hs
    simp [loopM]
  | succ n ih =>
    intro u s hs
    cases u
    rw [loopM_succ]
    simp only [bind, StateT.bind, Except.bind]
    have hb := hbody () s hs
    cases h : body () s with
    | error e => simp
    | ok val =>
      rcases val with ⟨lc, s'⟩
      simp only [h] at hb
      rcases lc with _ | a | a
      all_goals dsimp only
      all_goals simp only [LoopControl.post] at hb
      · -- continue
        exact ih () s' hb
      · -- break
        simp only [pure, StateT.pure, Except.pure]
        exact hb
      · -- return
        simp only [pure, StateT.pure, Except.pure]
        exact hb

/-- `stateLoopM_hoare`: state-variable loop with a state-indexed invariant.
    `I : Nat → FunctionState Regs → Prop` where the `Nat` indexes the CFG
    entry point (for State-Variable Encoding of Irreducible Loops).

    Reduced to `loopM_hoare` by lifting to the existential invariant
    `J s := ∃ k, I k s`. Not tagged with `aesop`. -/
theorem stateLoopM_hoare
    {I : Nat → FunctionState Regs → Prop}
    {Q : α → FunctionState Regs → Prop}
    {body : Unit → EffectStack Regs Ret (LoopControl α)}
    (hbody : ∀ u n, HoareM (I n) (body u)
               (LoopControl.post (fun s' => ∃ n', I n' s') Q))
    (n : Nat) :
    ∀ fuel u, HoareM (I n) (stateLoopM fuel body u) Q := by
  intro fuel u
  rw [stateLoopM_eq_loopM]
  -- Lift to the existential invariant J s := ∃ k, I k s.
  have hJ : ∀ u, HoareM (fun s => ∃ k, I k s) (body u)
                  (LoopControl.post (fun s' => ∃ k, I k s') Q) := by
    intro u s ⟨k, hk⟩
    have hb := hbody u k s hk
    rcases h : body u s with ⟨e⟩ | ⟨lc, s'⟩
    · trivial
    · simp only [h] at hb
      rcases lc with _ | a | a
      · simp only [LoopControl.post] at hb ⊢; exact hb
      · exact hb
      · exact hb
  have hloop := loopM_hoare (I := fun s => ∃ k, I k s) (Q := Q) hJ fuel u
  intro s hs
  exact hloop s ⟨n, hs⟩

end LoopLemma

end Bitlib
