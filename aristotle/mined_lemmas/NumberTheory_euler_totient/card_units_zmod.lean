/-
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace NumberTheory

/-- The group of units of `ZMod n` has order `Nat.totient n`, for `n > 0`. -/

theorem card_units_zmod (n : ℕ) [NeZero n] :
    Fintype.card (ZMod n)ˣ = Nat.totient n := by
  haveI : Fact (0 < n) := ⟨Nat.pos_of_ne_zero (NeZero.ne n)⟩
  exact ZMod.card_units_eq_totient n

/-- Euler's theorem, unit-group form: any unit of `ZMod n` raised to the power
`Nat.totient n` is `1`. -/
