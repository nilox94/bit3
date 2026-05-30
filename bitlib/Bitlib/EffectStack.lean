import Bitlib.LLVMType
import Aesop

-- Declared here (not in `Hoare.lean`) because `declare_aesop_rule_sets` is
-- only visible to files that *import* the declaring module.
declare_aesop_rule_sets [BitcHoare]

namespace Bitlib

/-- Control flow directives for loops. -/
inductive LoopControl (α : Type) where
  | continue : LoopControl α
  | «break»  : α → LoopControl α
  | «return» : α → LoopControl α

/-- The kind of Undefined Behavior encountered. -/
inductive UBKind where
  | divisionByZero
  | outOfBounds
  | nullPointerDereference
  /-- Fuel exhaustion: a `loopM` ran out of fuel before reaching `break`/`return`.
      This makes `loopM` total — non-terminating loops are observable as UB
      rather than wedging the kernel. -/
  | timeout

/-- The return value of a function, or UB. -/
abbrev ReturnOrUB (Ret : Type) (α : Type) := Except (Ret ⊕ UBKind) α

/-- FunctionState models the local state of a translated function. -/
structure FunctionState (Registers : Type) where
  /-- Register file for the current function. -/
  regs : Registers
  /-- Residual memory map (address → value) after mem2reg. -/
  memory : List (Nat × Int) -- Residual memory map (Finmap Nat Int)

/-- The Effect Stack type. -/
abbrev EffectStack (Regs : Type) (Ret : Type) (α : Type) :=
  StateT (FunctionState Regs) (ReturnOrUB Ret) α

/-- Postcondition pattern shared by `loopM_hoare` and its callers.

    `LoopControl.post I Q lc s'` is the natural postcondition for a loop
    body: on `continue`, the invariant `I` must hold at the post-state `s'`;
    on `break a` or `return a`, the outer `Q a s'` must hold.

    Factored as a top-level function so that the auxiliary `match` Lean
    auto-generates is identical at all use sites. Without this, the
    auto-generated `match_N` aux defs differ per enclosing declaration and
    unification between a user's body-lemma and `loopM_hoare`'s premise
    fails. -/
def LoopControl.post {Regs α : Type}
    (I : FunctionState Regs → Prop)
    (Q : α → FunctionState Regs → Prop) :
    LoopControl α → FunctionState Regs → Prop
  | .continue, s' => I s'
  | .break a,  s' => Q a s'
  | .return a, s' => Q a s'

/--
  The `loopM` combinator executes a body until it returns `break` or `return`,
  looping on `continue`. It is **total**: a `fuel : Nat` parameter bounds the
  number of iterations, and fuel exhaustion produces `UBKind.timeout`.

  Specialised to `EffectStack` so the `timeout` UB constructor is in scope.
-/
def loopM {Regs Ret α : Type}
    (fuel : Nat)
    (body : Unit → EffectStack Regs Ret (LoopControl α)) :
    Unit → EffectStack Regs Ret α :=
  match fuel with
  | 0          => fun _ _ => .error (.inr .timeout)
  | fuel' + 1  => fun () => do
      match (← body ()) with
      | LoopControl.continue => loopM fuel' body ()
      | LoopControl.break a  => pure a
      | LoopControl.return a => pure a

/--
  The `phi` combinator selects between two values based on a boolean condition.
  It models the LLVM `phi` node for conditional values.
-/
def phi {α : Type} (true_val false_val : α) (cond : Bool) : α :=
  if cond then true_val else false_val

/--
  `stateLoopM` is a derived form of `loopM` that threads a state through the loop.
  It is used for State-Variable Encoding of irreducible CFGs.
-/
def stateLoopM {Regs Ret α : Type}
    (fuel : Nat)
    (body : Unit → EffectStack Regs Ret (LoopControl α)) :
    Unit → EffectStack Regs Ret α :=
  loopM fuel body

theorem stateLoopM_eq_loopM {Regs Ret α : Type}
    (fuel : Nat)
    (body : Unit → EffectStack Regs Ret (LoopControl α)) :
  stateLoopM fuel body = loopM fuel body := rfl

/-- One-step unfolding of `loopM` at successor fuel. Holds definitionally. -/
theorem loopM_succ {Regs Ret α : Type}
    (fuel : Nat)
    (body : Unit → EffectStack Regs Ret (LoopControl α))
    (s : FunctionState Regs) :
    loopM (fuel + 1) body () s =
      (do
        match (← body ()) with
        | LoopControl.continue => loopM fuel body ()
        | LoopControl.break a  => pure a
        | LoopControl.return a => pure a) s := rfl

/-- Fuel exhaustion yields `timeout` UB. Holds definitionally. -/
theorem loopM_zero {Regs Ret α : Type}
    (body : Unit → EffectStack Regs Ret (LoopControl α))
    (s : FunctionState Regs) :
    loopM 0 body () s = .error (.inr .timeout) := rfl

end Bitlib
