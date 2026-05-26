import Bitlib.Hoare
open Bitlib

-- ---------------------------------------------------------------------------
-- HoareM proposition is defined and has the right type
-- ---------------------------------------------------------------------------

#check @HoareM
example : Prop := HoareM (Regs := Unit) (Ret := Int) (α := Unit)
  (fun _ => True) (pure ()) (fun _ _ => True)

-- ---------------------------------------------------------------------------
-- skip_hoare — pure satisfies any Q that holds for a in s
-- ---------------------------------------------------------------------------

example : HoareM (Regs := Unit) (Ret := Int)
    (fun _ => True)
    (pure 42 : EffectStack Unit Int Int)
    (fun v _ => v = 42) := by
  apply skip_hoare; intros; rfl

-- Same example, dispatched purely by aesop.
example : HoareM (Regs := Unit) (Ret := Int)
    (fun _ => True)
    (pure 42 : EffectStack Unit Int Int)
    (fun v _ => v = 42) := by
  aesop (rule_sets := [BitcHoare])

-- ---------------------------------------------------------------------------
-- modify_hoare — modify updates state correctly
-- ---------------------------------------------------------------------------

structure TestRegs where
  x : Int

example : HoareM (Regs := TestRegs) (Ret := Int)
    (fun s => s.regs.x = 0)
    (modify (fun s => { s with regs := { x := 1 } }) : EffectStack TestRegs Int Unit)
    (fun _ s => s.regs.x = 1) := by
  apply modify_hoare; intros; simp

-- ---------------------------------------------------------------------------
-- seq_hoare — WLP-style sequential composition
-- ---------------------------------------------------------------------------

-- No `(R := ...)` intermediate — WLP passes the post-state of the first leg
-- directly through the inner `HoareM`. `aesop (rule_sets := [BitcHoare])`
-- chains the structural lemmas mechanically.
example : HoareM (Regs := TestRegs) (Ret := Int)
    (fun s => s.regs.x = 0)
    (do
      modify (fun s => { s with regs := { x := 1 } })
      modify (fun s => { s with regs := { x := s.regs.x + 1 } })
      : EffectStack TestRegs Int Unit)
    (fun _ s => s.regs.x = 2) := by
  aesop (rule_sets := [BitcHoare])

-- ---------------------------------------------------------------------------
-- ifM_hoare — conditional branching
-- ---------------------------------------------------------------------------

example (b : Bool) : HoareM (Regs := TestRegs) (Ret := Int)
    (fun _ => True)
    (if b then
       (modify (fun s => { s with regs := { x := 1 } }) : EffectStack TestRegs Int Unit)
     else
       modify (fun s => { s with regs := { x := 0 } }))
    (fun _ s => s.regs.x = 1 ∨ s.regs.x = 0) := by
  aesop (rule_sets := [BitcHoare])

-- ---------------------------------------------------------------------------
-- loopM_hoare — loop with invariant (manual injection point)
-- ---------------------------------------------------------------------------

structure CounterRegs where
  n : Int

-- Count from 0 up to 5 inside the EffectStack. Fuel is arbitrary, ≥ 5.
example : HoareM (Regs := CounterRegs) (Ret := Int)
    (fun s => 0 ≤ s.regs.n ∧ s.regs.n ≤ 5)
    (loopM 10 (fun _ => do
      let s ← get
      if s.regs.n < 5 then do
        modify (fun s => { s with regs := { n := s.regs.n + 1 } })
        pure LoopControl.continue
      else
        pure (LoopControl.break s.regs.n)) ()
    : EffectStack CounterRegs Int Int)
    (fun v _ => v = 5) := by
  apply @loopM_hoare CounterRegs Int Int
    (I := fun s => 0 ≤ s.regs.n ∧ s.regs.n ≤ 5)
    (Q := fun v _ => v = 5)
  intro u s hs
  obtain ⟨h0, hn⟩ := hs
  simp only [bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
             pure, Except.pure, LoopControl.post]
  split
  · rename_i a s' h
    by_cases hlt : s.regs.n < 5
    · simp only [hlt, if_true] at h
      simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.bind,
            StateT.pure] at h
      obtain ⟨ha, hs'⟩ := Prod.mk.inj (Except.ok.inj h)
      subst ha; subst hs'; refine ⟨?_, ?_⟩ <;> (simp; omega)
    · simp only [hlt, if_false] at h
      simp [StateT.pure] at h
      obtain ⟨ha, hs'⟩ := Prod.mk.inj (Except.ok.inj h)
      subst ha; subst hs'; simp; omega
  · trivial

-- ---------------------------------------------------------------------------
-- stateLoopM_hoare — state-indexed invariant
-- ---------------------------------------------------------------------------

example : HoareM (Regs := CounterRegs) (Ret := Int)
    (fun s => 0 ≤ s.regs.n ∧ s.regs.n ≤ 3)
    (stateLoopM 10 (fun _ => do
      let s ← get
      if s.regs.n < 3 then do
        modify (fun s => { s with regs := { n := s.regs.n + 1 } })
        pure LoopControl.continue
      else
        pure (LoopControl.break s.regs.n)) ()
    : EffectStack CounterRegs Int Int)
    (fun v _ => v = 3) := by
  apply @stateLoopM_hoare CounterRegs Int Int
    (I := fun _ s => 0 ≤ s.regs.n ∧ s.regs.n ≤ 3)
    (Q := fun v _ => v = 3)
    (n := 0)
  intro u n s hs
  obtain ⟨h0, hn⟩ := hs
  simp only [bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
             pure, Except.pure, LoopControl.post]
  split
  · rename_i a s' h
    by_cases hlt : s.regs.n < 3
    · simp only [hlt, if_true] at h
      simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.bind,
            StateT.pure] at h
      obtain ⟨ha, hs'⟩ := Prod.mk.inj (Except.ok.inj h)
      subst ha; subst hs'
      refine ⟨0, ?_, ?_⟩ <;> (simp; omega)
    · simp only [hlt, if_false] at h
      simp [StateT.pure] at h
      obtain ⟨ha, hs'⟩ := Prod.mk.inj (Except.ok.inj h)
      subst ha; subst hs'; simp; omega
  · trivial

-- ---------------------------------------------------------------------------
-- store_hoare and load_hoare
-- ---------------------------------------------------------------------------

example : HoareM (Regs := Unit) (Ret := Int)
    (fun _ => True)
    (modify (fun s => { s with memory := (42, 99) :: s.memory.filter (fun p => p.1 ≠ 42) })
      : EffectStack Unit Int Unit)
    (fun _ s => s.memory.find? (fun p => p.1 == 42) = some (42, 99)) := by
  apply store_hoare
  intro s _
  simp [List.find?]

-- ---------------------------------------------------------------------------
-- Factorial proof using Hoare logic
-- This is the key acceptance criterion from issue #5.
-- ---------------------------------------------------------------------------

structure FactRegs where
  n   : Int
  acc : Int

/-- Body of the factorial loop: decrement `n`, multiply `acc`, until `n ≤ 0`. -/
def factBody : Unit → EffectStack FactRegs Int (LoopControl Int) := fun _ => do
  let s ← get
  if s.regs.n ≤ 0 then
    pure (LoopControl.break s.regs.acc)
  else do
    modify (fun s => { s with regs :=
      { n := s.regs.n - 1, acc := s.regs.acc * s.regs.n } })
    pure LoopControl.continue

/-- Monadic factorial: computes n! iteratively. Fuel must dominate n. -/
def factM (n : Int) (fuel : Nat) : EffectStack FactRegs Int Int :=
  do
    modify (fun s => { s with regs := { n := n, acc := 1 } })
    loopM fuel factBody ()

/-- Mathematical factorial for the spec -/
def fact : Nat → Int
  | 0     => 1
  | n + 1 => (n + 1) * fact n

/-- Invariant: acc * n! = initial_n! -/
def factInv (initial : Int) (s : FunctionState FactRegs) : Prop :=
  0 ≤ s.regs.n ∧ s.regs.acc * fact s.regs.n.toNat = fact initial.toNat

/-- `factM n` computes `n!` for any fuel large enough to run the loop.
    Fuel exhaustion (`UBKind.timeout`) is vacuously satisfied — partial
    correctness, total `loopM`.

    The proof uses WLP `seq_hoare` for the seeding `modify`, then specialises
    `loopM_hoare` at the concrete post-`modify` state. The loop invariant is
    the standard `acc * n! = initial_n!`. -/
theorem factM_correct (n : Int) (fuel : Nat) (hn : 0 ≤ n) :
    HoareM
      (fun _ => True)
      (factM n fuel)
      (fun v _ => v = fact n.toNat) := by
  -- Step 1: WLP-chain the seeding `modify` with the loop.
  unfold factM
  apply seq_hoare
  apply modify_hoare
  intro s _ s' hss'
  subst hss'
  -- Step 2: build the body's invariant lemma inline. We must avoid a
  -- separate top-level lemma because Lean's elaborator otherwise has
  -- trouble unifying its postcondition with the outer `fun v _ => v = ...`.
  have hbody : ∀ u, HoareM (factInv n) (factBody u)
        (LoopControl.post (factInv n) (fun v _ => v = fact n.toNat)) := by
    intro u s hs
    unfold factBody
    obtain ⟨hnn, hinv⟩ := hs
    simp only [bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
               pure, Except.pure, factInv, LoopControl.post]
    split
    · rename_i a s'' h
      by_cases hle : s.regs.n ≤ 0
      · -- n ≤ 0: break with `acc = fact n`.
        simp only [hle, if_true] at h
        simp [StateT.pure] at h
        obtain ⟨ha, hs''⟩ := Prod.mk.inj (Except.ok.inj h)
        subst ha; subst hs''; simp
        have hn0 : s.regs.n = 0 := by omega
        simp [hn0, fact] at hinv
        exact hinv
      · -- n > 0: continue with `n' = n - 1`, `acc' = acc * n`.
        have hgt : 0 < s.regs.n := by omega
        simp only [show ¬ s.regs.n ≤ 0 from by omega, if_false] at h
        simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.bind,
              StateT.pure] at h
        obtain ⟨ha, hs''⟩ := Prod.mk.inj (Except.ok.inj h)
        subst ha; subst hs''; simp
        refine ⟨by omega, ?_⟩
        have hfact : fact s.regs.n.toNat = s.regs.n * fact (s.regs.n.toNat - 1) := by
          cases h : s.regs.n.toNat with
          | zero => omega
          | succ k =>
            simp [fact]
            have hk1 : s.regs.n = k + 1 := by omega
            rw [hk1]
        rw [hfact, ← Int.mul_assoc] at hinv
        exact hinv
    · trivial
  -- Step 3: invoke `loopM_hoare` on the concrete post-`modify` state.
  exact loopM_hoare (I := factInv n) hbody fuel () _ (by simp [factInv, hn])

-- ---------------------------------------------------------------------------
-- Axiom audit: the Hoare layer must add zero axioms to the TCB.
-- Each `#print axioms` line is a compile-time assertion; CI surfaces drift.
-- ---------------------------------------------------------------------------

#print axioms HoareM
#print axioms loopM
#print axioms loopM_hoare
#print axioms stateLoopM_hoare
#print axioms seq_hoare
#print axioms skip_hoare
#print axioms modify_hoare
#print axioms ifM_hoare
#print axioms store_hoare
#print axioms load_hoare
#print axioms factM_correct
