import Mathlib
open Matrix

namespace C3.Alg4

/-- Chinese Remainder Theorem: for coprime `m` and `n`, `ZMod (m*n)` is isomorphic
as a ring to `ZMod m × ZMod n`. -/

theorem crt_ring (m n : ℕ) (h : Nat.Coprime m n) :
    Nonempty (ZMod (m*n) ≃+* ZMod m × ZMod n) :=
  ⟨ZMod.chineseRemainder h⟩

/-- The unit group of `ZMod n` has order `φ n`. -/
