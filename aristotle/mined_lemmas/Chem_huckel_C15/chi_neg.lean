import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The primitive 15-th root of unity `exp(2πi/15)`. -/

lemma chi_neg (a : ZMod 15) : chi (-a) = (chi a)⁻¹ := by
  have : chi (-a) * chi a = 1 := by rw [← chi_add]; simp [chi_zero]
  field_simp [chi_ne_zero a] at this ⊢
  linear_combination this

/-- Character sum orthogonality. -/
