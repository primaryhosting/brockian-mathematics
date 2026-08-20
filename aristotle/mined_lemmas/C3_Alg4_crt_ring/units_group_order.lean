import Mathlib
open Matrix

namespace C3.Alg4

/-- Chinese Remainder Theorem: for coprime `m` and `n`, `ZMod (m*n)` is isomorphic
as a ring to `ZMod m × ZMod n`. -/

theorem units_group_order (n : ℕ) [NeZero n] :
    Fintype.card (ZMod n)ˣ = Nat.totient n :=
  ZMod.card_units_eq_totient n

/-- The determinant is invariant under transposition. -/
