import Bitlib.LLVMType

namespace Bitlib

/-- Control flow directives for loops. -/
inductive LoopControl (α : Type) where
  | continue : LoopControl α
  | «break»  : α → LoopControl α
  | «return» : α → LoopControl α

/-- 
  The `loopM` combinator executes a body until it returns `break` or `return`.
  It loops on `continue`.
  Note: We use `partial` because we don't prove termination here.
-/
partial def loopM {m : Type → Type} [Monad m] {α : Type} [Inhabited (m α)] (body : Unit → m (LoopControl α)) : Unit → m α
  | () => do
    match (← body ()) with
    | LoopControl.continue => loopM body ()
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
partial def stateLoopM {m : Type → Type} [Monad m] {α : Type} [Inhabited (m α)] (body : Unit → m (LoopControl α)) : Unit → m α :=
  loopM body

theorem stateLoopM_eq_loopM {m : Type → Type} [Monad m] {α : Type} [Inhabited (m α)] (body : Unit → m (LoopControl α)) :
  stateLoopM body = loopM body := rfl

/-- The kind of Undefined Behavior encountered. -/
inductive UBKind where
  | divisionByZero
  | outOfBounds
  | nullPointerDereference

/-- The return value of a function, or UB. -/
abbrev ReturnOrUB (Ret : Type) (α : Type) := Except (Ret ⊕ UBKind) α

/-- FunctionState models the local state of a translated function. -/
structure FunctionState (Registers : Type) where
  regs : Registers
  memory : List (Nat × Int) -- Residual memory map (Finmap Nat Int)

/-- The Effect Stack type. -/
abbrev EffectStack (Regs : Type) (Ret : Type) (α : Type) :=
  StateT (FunctionState Regs) (ReturnOrUB Ret) α

end Bitlib
