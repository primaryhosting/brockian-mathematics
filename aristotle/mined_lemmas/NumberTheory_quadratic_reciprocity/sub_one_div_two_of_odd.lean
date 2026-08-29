/-
# Quadratic Reciprocity
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace NumberTheory

/-- For an odd natural number `n`, `(n - 1) / 2 = n / 2` (natural division/subtraction). -/

lemma sub_one_div_two_of_odd {n : ℕ} (hn : Odd n) : (n - 1) / 2 = n / 2 := by
  obtain ⟨k, hk⟩ := hn
  subst hk
  omega

/-- **Gauss's law of quadratic reciprocity**: for distinct odd primes `p` and `q`,
`legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2))`. -/
