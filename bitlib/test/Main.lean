-- bitlib test suite
import Bitlib.LLVMType
import Bitlib.EffectStack

open Bitlib

-- ---------------------------------------------------------------------------
-- LLVMType inductive
-- ---------------------------------------------------------------------------

-- The three constructors must exist and be distinguishable.
#guard (LLVMType.iN 32 != LLVMType.void)
#guard (LLVMType.iN 1  == LLVMType.iN 1)
#guard (LLVMType.function [LLVMType.iN 32, LLVMType.iN 32] (LLVMType.iN 32) != LLVMType.void)

-- ---------------------------------------------------------------------------
-- LLVMRepr typeclass
-- ---------------------------------------------------------------------------

-- iN maps to Int
example : LLVMRepr.Carrier (t := LLVMType.iN 32) = Int := rfl
-- void maps to Unit
example : LLVMRepr.Carrier (t := LLVMType.void) = Unit := rfl
-- function maps to the carrier of its return type
example : LLVMRepr.Carrier (t := LLVMType.function [LLVMType.iN 32] (LLVMType.iN 64)) = Int := rfl
example : LLVMRepr.Carrier (t := LLVMType.function [] LLVMType.void) = Unit := rfl

-- ---------------------------------------------------------------------------
-- wrapI — boundary values for widths 1, 8, 32, 64
-- ---------------------------------------------------------------------------

-- Width 1: range [-1, 0]
#guard wrapI 1 0  ==  0
#guard wrapI 1 1  == -1   -- 1 >= 2^0 = 1, so subtract 2 -> -1
#guard wrapI 1 (-1) == -1
#guard wrapI 1 2  ==  0   -- 2 mod 2 = 0

-- Width 8: range [-128, 127]
#guard wrapI 8 0    ==   0
#guard wrapI 8 127  == 127
#guard wrapI 8 128  == -128   -- overflow wraps to min
#guard wrapI 8 (-128) == -128
#guard wrapI 8 (-129) == 127  -- underflow wraps to max
#guard wrapI 8 255  ==  -1    -- 0xFF signed = -1
#guard wrapI 8 256  ==   0    -- full wrap-around

-- Width 32: range [-2^31, 2^31 - 1]
#guard wrapI 32 0                  ==  0
#guard wrapI 32 2147483647         ==  2147483647
#guard wrapI 32 2147483648         == -2147483648   -- INT_MAX + 1 wraps
#guard wrapI 32 (-2147483648)      == -2147483648
#guard wrapI 32 (-2147483649)      ==  2147483647   -- INT_MIN - 1 wraps

-- Width 64: range [-2^63, 2^63 - 1]
#guard wrapI 64 0                         ==  0
#guard wrapI 64 9223372036854775807       ==  9223372036854775807
#guard wrapI 64 9223372036854775808       == -9223372036854775808
#guard wrapI 64 (-9223372036854775808)    == -9223372036854775808
#guard wrapI 64 (-9223372036854775809)    ==  9223372036854775807

-- ---------------------------------------------------------------------------
-- toBool / ofBool coercion
-- ---------------------------------------------------------------------------

-- Use fully-qualified name to avoid ambiguity with Lean's built-in ToBool
#guard Bitlib.toBool 0  == false
#guard Bitlib.toBool 1  == true
#guard Bitlib.toBool (-1) == true
#guard Bitlib.toBool 42 == true

#guard ofBool false == 0
#guard ofBool true  == 1

-- Round-trip: ofBool . toBool is identity on {0, 1}
#guard ofBool (Bitlib.toBool 0) == 0
#guard ofBool (Bitlib.toBool 1) == 1

-- ---------------------------------------------------------------------------
-- EffectStack: LoopControl
-- ---------------------------------------------------------------------------

#check Bitlib.LoopControl.continue (α := Int)
#check Bitlib.LoopControl.break (α := Int)
#check Bitlib.LoopControl.return (α := Int)

-- loopM terminates when returning break or return
#eval Id.run do
  let res ← Bitlib.loopM (m := Id) (fun _ => pure (Bitlib.LoopControl.break 42)) ()
  pure (res == 42)

-- phi combinator test
#eval Bitlib.phi 1 2 true == 1
#eval Bitlib.phi 1 2 false == 2

-- stateLoopM test
#eval Id.run do
  let res ← Bitlib.stateLoopM (m := Id) (fun _ => pure (Bitlib.LoopControl.break 42)) ()
  pure (res == 42)

-- EffectStack type test
def testEffectStack : Bitlib.EffectStack Unit Int Unit := do
  let s ← get
  set { s with regs := () }
  pure ()

-- loopM counting loop: counts from 0 to 4 and breaks at 5
-- Uses StateT to thread the counter through the loop
def countingLoop : StateT Nat Id Int :=
  Bitlib.loopM (m := StateT Nat Id) (fun _ => do
    let n ← get
    if n < 5 then
      set (n + 1)
      pure Bitlib.LoopControl.continue
    else
      pure (Bitlib.LoopControl.break n)) ()

#guard (countingLoop.run 0).1 == 5

-- ---------------------------------------------------------------------------
-- Storable stub -- just check it compiles and can be mentioned
-- ---------------------------------------------------------------------------

-- We can write an instance for a concrete type without providing any fields.
instance : Storable (LLVMType.iN 32) where

def main : IO Unit := do
  IO.println "bitlib tests: ok"
