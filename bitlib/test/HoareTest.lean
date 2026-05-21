import Bitlib.Hoare
open Bitlib

-- ---------------------------------------------------------------------------
-- TDD Cycle 1: HoareM proposition is defined and has the right type
-- ---------------------------------------------------------------------------

-- HoareM must be a Prop
#check @HoareM
-- HoareM P c Q : Prop
example : Prop := HoareM (Regs := Unit) (Ret := Int) (α := Unit)
  (fun _ => True) (pure ()) (fun _ _ => True)

-- ---------------------------------------------------------------------------
-- TDD Cycle 2: skip_hoare — pure satisfies any Q that holds for a in s
-- ---------------------------------------------------------------------------

example : HoareM (Regs := Unit) (Ret := Int)
    (fun _ => True)
    (pure 42 : EffectStack Unit Int Int)
    (fun v _ => v = 42) := by
  apply skip_hoare; intros; rfl

-- ---------------------------------------------------------------------------
-- TDD Cycle 3: modify_hoare — modify updates state correctly
-- ---------------------------------------------------------------------------

structure TestRegs where
  x : Int

example : HoareM (Regs := TestRegs) (Ret := Int)
    (fun s => s.regs.x = 0)
    (modify (fun s => { s with regs := { x := 1 } }) : EffectStack TestRegs Int Unit)
    (fun _ s => s.regs.x = 1) := by
  apply modify_hoare; intros s hs; simp [hs]

-- ---------------------------------------------------------------------------
-- TDD Cycle 4: seq_hoare — sequential composition
-- ---------------------------------------------------------------------------

example : HoareM (Regs := TestRegs) (Ret := Int)
    (fun s => s.regs.x = 0)
    (do
      modify (fun s => { s with regs := { x := 1 } })
      modify (fun s => { s with regs := { x := s.regs.x + 1 } })
      : EffectStack TestRegs Int Unit)
    (fun _ s => s.regs.x = 2) := by
  apply seq_hoare (R := fun _ s => s.regs.x = 1)
  · apply modify_hoare; intros s hs; simp [hs]
  · intro _
    apply modify_hoare; intros s hs; simp [hs]

-- ---------------------------------------------------------------------------
-- TDD Cycle 5: ifM_hoare — conditional branching
-- ---------------------------------------------------------------------------

example (b : Bool) : HoareM (Regs := TestRegs) (Ret := Int)
    (fun _ => True)
    (if b then
       (modify (fun s => { s with regs := { x := 1 } }) : EffectStack TestRegs Int Unit)
     else
       modify (fun s => { s with regs := { x := 0 } }))
    (fun _ s => s.regs.x = 1 ∨ s.regs.x = 0) := by
  apply ifM_hoare
  · intro _; apply modify_hoare; intros; exact Or.inl rfl
  · intro _; apply modify_hoare; intros; exact Or.inr rfl

-- ---------------------------------------------------------------------------
-- TDD Cycle 6: loopM_hoare — loop with invariant
-- ---------------------------------------------------------------------------

-- Count from 0 to 5 using loopM
structure CounterRegs where
  n : Int

example : HoareM (Regs := CounterRegs) (Ret := Int)
    (fun s => 0 ≤ s.regs.n ∧ s.regs.n ≤ 5)
    (loopM (m := EffectStack CounterRegs Int) (fun _ => do
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
    (body := fun _ => do
      let s ← get
      if s.regs.n < 5 then do
        modify (fun s => { s with regs := { n := s.regs.n + 1 } })
        pure LoopControl.continue
      else
        pure (LoopControl.break s.regs.n))
  intro u s hs
  obtain ⟨h0, hn⟩ := hs
  simp only [bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
             pure, Except.pure]
  split
  · rename_i a s' h
    by_cases hlt : s.regs.n < 5
    · simp only [hlt, if_true] at h
      simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.bind,
            StateT.pure] at h
      obtain ⟨ha, hs'⟩ := Prod.mk.inj (Except.ok.inj h)
      subst ha; subst hs'; simp; constructor; omega; omega
    · simp only [hlt, if_false] at h
      simp [StateT.pure] at h
      obtain ⟨ha, hs'⟩ := Prod.mk.inj (Except.ok.inj h)
      subst ha; subst hs'; simp; omega
  · trivial

-- ---------------------------------------------------------------------------
-- TDD Cycle 7: stateLoopM_hoare — state-indexed invariant
-- ---------------------------------------------------------------------------

example : HoareM (Regs := CounterRegs) (Ret := Int)
    (fun s => 0 ≤ s.regs.n ∧ s.regs.n ≤ 3)
    (stateLoopM (m := EffectStack CounterRegs Int) (fun _ => do
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
    (body := fun _ => do
      let s ← get
      if s.regs.n < 3 then do
        modify (fun s => { s with regs := { n := s.regs.n + 1 } })
        pure LoopControl.continue
      else
        pure (LoopControl.break s.regs.n))
    (n := 0)
  intro u n s hs
  obtain ⟨h0, hn⟩ := hs
  simp only [bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
             pure, Except.pure]
  split
  · rename_i a s' h
    by_cases hlt : s.regs.n < 3
    · simp only [hlt, if_true] at h
      simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.bind,
            StateT.pure] at h
      obtain ⟨ha, hs'⟩ := Prod.mk.inj (Except.ok.inj h)
      subst ha; subst hs'
      simp only []
      exact ⟨0, by omega, by omega⟩
    · simp only [hlt, if_false] at h
      simp [StateT.pure] at h
      obtain ⟨ha, hs'⟩ := Prod.mk.inj (Except.ok.inj h)
      subst ha; subst hs'
      simp only []
      omega
  · trivial

-- ---------------------------------------------------------------------------
-- TDD Cycle 8: store_hoare and load_hoare
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
-- TDD Cycle 9: Factorial proof using Hoare logic
-- This is the key acceptance criterion from issue #5.
-- ---------------------------------------------------------------------------

/-- Registers for the factorial function -/
structure FactRegs where
  n   : Int  -- current counter
  acc : Int  -- accumulator

/-- Monadic factorial: computes n! iteratively -/
def factM (n : Int) : EffectStack FactRegs Int Int :=
  do
    modify (fun s => { s with regs := { n := n, acc := 1 } })
    loopM (m := EffectStack FactRegs Int) (fun _ => do
      let s ← get
      if s.regs.n ≤ 0 then
        pure (LoopControl.break s.regs.acc)
      else do
        modify (fun s => { s with regs :=
          { n := s.regs.n - 1, acc := s.regs.acc * s.regs.n } })
        pure LoopControl.continue) ()

/-- Mathematical factorial for the spec -/
def fact : Nat → Int
  | 0     => 1
  | n + 1 => (n + 1) * fact n

/-- Invariant: acc * n! = initial_n! -/
def factInv (initial : Int) (s : FunctionState FactRegs) : Prop :=
  0 ≤ s.regs.n ∧ s.regs.acc * fact s.regs.n.toNat = fact initial.toNat

/-- Prove that factM n computes n! using Hoare logic -/
theorem factM_correct (n : Int) (hn : 0 ≤ n) :
    HoareM
      (fun _ => True)
      (factM n)
      (fun v _ => v = fact n.toNat) := by
  unfold factM
  -- Step 1: apply seq_hoare for the modify
  apply seq_hoare (R := fun _ => factInv n)
  · -- The modify establishes the invariant
    apply modify_hoare
    intro s _
    simp [factInv, fact, hn]
  · -- Step 2: apply loopM_hoare with the factorial invariant
    intro _
    apply @loopM_hoare FactRegs Int Int
      (I := factInv n)
      (Q := fun v _ => v = fact n.toNat)
      (body := fun _ => do
        let s ← get
        if s.regs.n ≤ 0 then
          pure (LoopControl.break s.regs.acc)
        else do
          modify (fun s => { s with regs :=
            { n := s.regs.n - 1, acc := s.regs.acc * s.regs.n } })
          pure LoopControl.continue)
    intro u s hs
    obtain ⟨hnn, hinv⟩ := hs
    simp only [bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
               pure, Except.pure, factInv]
    split
    · rename_i a s' h
      by_cases hle : s.regs.n ≤ 0
      · -- n ≤ 0, break with acc
        simp only [hle, if_true] at h
        simp [StateT.pure] at h
        obtain ⟨ha, hs'⟩ := Prod.mk.inj (Except.ok.inj h)
        subst ha; subst hs'; simp
        have hn0 : s.regs.n = 0 := by omega
        simp [hn0, fact] at hinv
        exact hinv
      · -- n > 0, continue
        have hgt : 0 < s.regs.n := by omega
        simp only [show ¬ s.regs.n ≤ 0 from by omega, if_false] at h
        simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.bind,
              StateT.pure] at h
        obtain ⟨ha, hs'⟩ := Prod.mk.inj (Except.ok.inj h)
        subst ha; subst hs'; simp
        constructor
        · omega
        · have hfact : fact s.regs.n.toNat = s.regs.n * fact (s.regs.n.toNat - 1) := by
            cases h : s.regs.n.toNat with
            | zero => omega
            | succ k =>
              simp [fact]
              have hk1 : s.regs.n = k + 1 := by omega
              rw [hk1]
          rw [hfact] at hinv
          rw [← Int.mul_assoc] at hinv
          exact hinv
    · trivial
