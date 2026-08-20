import Mathlib
/-!
# Chinese Remainder
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace NumberTheory

/-- **Chinese remainder theorem**: for coprime naturals `m` and `n`, the ring `ZMod (m * n)`
is isomorphic (as a ring) to the product ring `ZMod m × ZMod n`. -/

theorem chinese_remainder {m n : ℕ} (h : Nat.Coprime m n) :
    Nonempty (ZMod (m * n) ≃+* ZMod m × ZMod n) :=
  ⟨ZMod.chineseRemainder h⟩

/-- The isomorphism of `NumberTheory.chinese_remainder` can be taken to be the natural one,
given by the pair of reduction maps `ZMod (m * n) → ZMod m` and `ZMod (m * n) → ZMod n`. -/
