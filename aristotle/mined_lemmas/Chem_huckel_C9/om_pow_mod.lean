import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

noncomputable section

/-- A primitive 9-th root of unity. -/

lemma om_pow_mod (n : ℕ) : om ^ (n % 9) = om ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 9]
  rw [pow_add, pow_mul, om_pow_nine, one_pow, one_mul]

