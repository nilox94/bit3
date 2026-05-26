-- bitlib test suite
import Bitlib.LLVMType
import Bitlib.EffectStack
import Bitlib.Hoare
-- Elaborates the Hoare-logic proof examples (issue #5 acceptance criteria).
import HoareTest

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

#guard Bitlib.toBool 0  == false
#guard Bitlib.toBool 1  == true
#guard Bitlib.toBool (-1) == true
#guard Bitlib.toBool 42 == true

#guard ofBool false == 0
#guard ofBool true  == 1

#guard ofBool (Bitlib.toBool 0) == 0
#guard ofBool (Bitlib.toBool 1) == 1

-- ---------------------------------------------------------------------------
-- EffectStack: LoopControl
-- ---------------------------------------------------------------------------

#check Bitlib.LoopControl.continue (α := Int)
#check Bitlib.LoopControl.break (α := Int)
#check Bitlib.LoopControl.return (α := Int)

-- phi combinator test
#eval Bitlib.phi 1 2 true == 1
#eval Bitlib.phi 1 2 false == 2

-- ---------------------------------------------------------------------------
-- EffectStack: loopM smoke test (fuel-indexed, total)
-- ---------------------------------------------------------------------------

structure SmokeCounter where
  n : Int

/-- A loop that counts from 0 to 5 inside the `EffectStack`. -/
def countingLoop (fuel : Nat) : EffectStack SmokeCounter Int Int :=
  loopM fuel (fun _ => do
    let s ← get
    if s.regs.n < 5 then do
      modify (fun s => { s with regs := { n := s.regs.n + 1 } })
      pure LoopControl.continue
    else
      pure (LoopControl.break s.regs.n)) ()

-- With enough fuel, the loop finishes with `n = 5`.
#guard
  (match (countingLoop 10).run { regs := { n := 0 }, memory := [] } with
   | .ok (v, _) => v == 5
   | .error _   => false)

-- With insufficient fuel, the loop hits `.timeout`.
#guard
  (match (countingLoop 2).run { regs := { n := 0 }, memory := [] } with
   | .ok _              => false
   | .error (.inr .timeout) => true
   | .error _           => false)

-- `stateLoopM` is definitionally equal to `loopM`.
example (fuel : Nat) (body : Unit → EffectStack SmokeCounter Int (LoopControl Int)) :
    stateLoopM fuel body = loopM fuel body := rfl

-- EffectStack type test
def testEffectStack : Bitlib.EffectStack Unit Int Unit := do
  let s ← get
  set { s with regs := () }
  pure ()

-- ---------------------------------------------------------------------------
-- Storable stub
-- ---------------------------------------------------------------------------

instance : Storable (LLVMType.iN 32) where

def main : IO Unit := do
  IO.println "bitlib tests: ok"
