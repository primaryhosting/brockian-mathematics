/-
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace NumberTheory

/-- **Euler's theorem**, unit-group form: for a unit `u` of `ZMod n`,
`u ^ Nat.totient n = 1`. -/

theorem isUnit_natCast_of_coprime {a n : ℕ} (h : Nat.Coprime a n) : IsUnit (a : ZMod n) :=
  (ZMod.isUnit_iff_coprime a n).2 h

/-- **Euler's theorem**, congruence form: if `a` and `n` are coprime, then
`a ^ Nat.totient n ≡ 1 [MOD n]`.  Derived from `euler_totient` above. -/
