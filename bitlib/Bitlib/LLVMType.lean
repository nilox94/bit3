/-!
# Bitlib.LLVMType

Type-system foundation for the bit3 Translator.

## Design decisions (see ADR-0003)
- LLVM integer types are represented by Lean's unbounded `Int`.
- Modular wrapping is applied explicitly via `wrapI` at every arithmetic
  operation, so that `omega` can discharge no-overflow goals automatically.
- `BitVec` is left as an upgrade path for exact bit-manipulation proofs.

## V0 scope
- `LLVMType` inductive: `iN`, `void`, `function`
- `LLVMRepr` typeclass: maps each constructor to its Lean carrier
- `wrapI`: signed two's-complement modular reduction
- `i1` / `toBool`: coercion between `Int` and `Bool`
- `Storable`: stub typeclass, reserved for V1 typed-memory extension
-/

namespace Bitlib

-- ---------------------------------------------------------------------------
-- 1. Inductive type hierarchy
-- ---------------------------------------------------------------------------

/-- The LLVM types supported by the Translator in V0.

- `iN w` — a signed integer of bit-width `w` (w > 0).
- `void`  — the unit type; used as the return type of void functions.
- `function args ret` — a function from a list of argument types to a return
  type.  Stored as a `List LLVMType × LLVMType` pair so that the Translator
  can pattern-match on the signature without unfolding a dependent function.
-/
inductive LLVMType : Type where
  | iN       : Nat → LLVMType
  | void     : LLVMType
  | function : List LLVMType → LLVMType → LLVMType
  deriving Repr

-- Lean 4 cannot auto-derive `DecidableEq` for `LLVMType` because the
-- `function` constructor embeds a `List LLVMType`, making the type
-- mutually recursive with `List`.  We provide the instance by structural
-- recursion.
mutual
  instance instDecidableEqLLVMType : DecidableEq LLVMType
    | LLVMType.iN w₁,            LLVMType.iN w₂            =>
        if h : w₁ = w₂ then isTrue (congrArg LLVMType.iN h)
        else isFalse (fun heq => h (by cases heq; rfl))
    | LLVMType.void,             LLVMType.void             => isTrue rfl
    | LLVMType.function as₁ r₁, LLVMType.function as₂ r₂  =>
        match instDecidableEqLLVMTypeList as₁ as₂,
              instDecidableEqLLVMType r₁ r₂ with
        | isTrue ha, isTrue hr =>
            isTrue (by subst ha; subst hr; rfl)
        | isFalse ha, _ =>
            isFalse (fun heq => ha (by cases heq; rfl))
        | _, isFalse hr =>
            isFalse (fun heq => hr (by cases heq; rfl))
    | LLVMType.iN _,             LLVMType.void             =>
        isFalse (by intro h; cases h)
    | LLVMType.iN _,             LLVMType.function _ _     =>
        isFalse (by intro h; cases h)
    | LLVMType.void,             LLVMType.iN _             =>
        isFalse (by intro h; cases h)
    | LLVMType.void,             LLVMType.function _ _     =>
        isFalse (by intro h; cases h)
    | LLVMType.function _ _,     LLVMType.iN _             =>
        isFalse (by intro h; cases h)
    | LLVMType.function _ _,     LLVMType.void             =>
        isFalse (by intro h; cases h)

  instance instDecidableEqLLVMTypeList : DecidableEq (List LLVMType)
    | [],      []      => isTrue rfl
    | _ :: _,  []      => isFalse (by intro h; cases h)
    | [],      _ :: _  => isFalse (by intro h; cases h)
    | x :: xs, y :: ys =>
        match instDecidableEqLLVMType x y,
              instDecidableEqLLVMTypeList xs ys with
        | isTrue hx, isTrue hxs =>
            isTrue (by subst hx; subst hxs; rfl)
        | isFalse hx, _ =>
            isFalse (fun heq => hx (by cases heq; rfl))
        | _, isFalse hxs =>
            isFalse (fun heq => hxs (by cases heq; rfl))
end

-- ---------------------------------------------------------------------------
-- 2. LLVMRepr typeclass
-- ---------------------------------------------------------------------------

/-- Maps an `LLVMType` to the Lean type that carries its values at
verification time.

| LLVM type | Lean carrier |
|-----------|--------------|
| `iN _`    | `Int`        |
| `void`    | `Unit`       |
| `function args ret` | carrier of `ret` (the Translator always emits
  fully-applied call sites, so the function type itself need not be reified) |

Note: the `function` instance returns the carrier of the *return* type.
This is intentional: the Translator always generates fully-applied calls, so
the function type itself never needs to be reified as a Lean function type in
the verification layer.
-/
class LLVMRepr (t : LLVMType) where
  /-- The Lean type that carries values of LLVM type `t`. -/
  Carrier : Type

instance (w : Nat) : LLVMRepr (LLVMType.iN w) where
  Carrier := Int

instance : LLVMRepr LLVMType.void where
  Carrier := Unit

instance (args : List LLVMType) (ret : LLVMType) [LLVMRepr ret] :
    LLVMRepr (LLVMType.function args ret) where
  Carrier := LLVMRepr.Carrier (t := ret)

-- ---------------------------------------------------------------------------
-- 3. wrapI — signed two's-complement modular reduction
-- ---------------------------------------------------------------------------

/-- `wrapI w x` reduces `x` to the signed two's-complement range for a
`w`-bit integer, i.e. `[−2^(w−1), 2^(w−1) − 1]`.

The formula is:
  1. Compute `m = 2^w` (the modulus).
  2. Reduce `x` modulo `m` into `[0, m)` using `x % m` with Lean's
     non-negative-remainder convention for `Int`.
  3. If the result is ≥ `2^(w−1)`, subtract `m` to bring it into the
     negative half.

For `w = 0` the result is always `0` (degenerate case, not used in practice).
-/
def wrapI (w : Nat) (x : Int) : Int :=
  if w = 0 then 0
  else
    let m : Int := Int.ofNat (2 ^ w)
    -- Int.emod always returns a non-negative result when the divisor is
    -- positive, so r ∈ [0, m).
    let r := x % m
    let r' := if r < 0 then r + m else r
    if r' ≥ m / 2 then r' - m else r'

-- ---------------------------------------------------------------------------
-- 4. i1 / toBool coercion
-- ---------------------------------------------------------------------------

/-- The canonical LLVM 1-bit integer type. -/
abbrev i1 : LLVMType := LLVMType.iN 1

/-- Coerce an LLVM `i1` value (represented as `Int`) to a Lean `Bool`.
  `0` maps to `false`; any other value maps to `true`.  The Translator
  emits this coercion at every conditional branch. -/
def toBool (x : Int) : Bool := x ≠ 0

/-- Coerce a `Bool` back to an LLVM `i1` value. -/
def ofBool (b : Bool) : Int := if b then 1 else 0

-- ---------------------------------------------------------------------------
-- 5. Storable — V1 extension point for typed memory
-- ---------------------------------------------------------------------------

/-- Stub typeclass reserved for V1.

In V1 the Translator will need to read and write typed values through a
byte-addressed memory model.  `Storable` will provide the serialisation
width (in bytes) and the load/store operations.  It is left intentionally
empty in V0 so that downstream modules can already mention it in type
signatures without pulling in unimplemented machinery.
-/
class Storable (t : LLVMType) : Prop where

end Bitlib
