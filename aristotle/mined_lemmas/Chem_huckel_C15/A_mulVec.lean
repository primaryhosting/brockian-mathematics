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

lemma A_mulVec (x : ZMod 15 → ℂ) (i : ZMod 15) :
    (A *ᵥ x) i = x (i - 1) + x (i + 1) := by
  simp only [Matrix.mulVec, dotProduct, A_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

