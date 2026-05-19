# Integer Representation via Int with Modular Wrappers

We decided to represent LLVM integer types using Lean's unbounded `Int` type, applying explicit modular wrapping functions (e.g., `wrapI`) at every arithmetic operation, rather than using Lean's native `BitVec` type.

Lean 4 provides `BitVec`, which perfectly models machine integer semantics and native wrapping. However, the primary proof automation tactics for arithmetic in Lean (`omega` and `linarith`) work natively on `Int` and `Nat`, not `BitVec`. Because the vast majority of verified programs assume no overflow (often relying on LLVM's `nsw`/`nuw` flags), using `Int` allows the `omega` tactic to discharge arithmetic goals effortlessly, provided the no-overflow side conditions are met. We traded exact bit-level ergonomics for significantly easier proof automation in the common case. `BitVec` remains an upgrade path for specific functions requiring exact bit manipulation.
