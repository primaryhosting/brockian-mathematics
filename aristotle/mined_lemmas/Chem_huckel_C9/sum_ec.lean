import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- A primitive ninth root of unity. -/

lemma sum_ec (c : ZMod 9) : ∑ x : ZMod 9, ec (c * x) = if c = 0 then 9 else 0 := by
  by_cases hc : c = 0
  · simp [hc, ec_zero]
  · simp [hc, sum_ec_ne_zero hc]

/-- Fourier inversion on `ZMod 9`. -/
