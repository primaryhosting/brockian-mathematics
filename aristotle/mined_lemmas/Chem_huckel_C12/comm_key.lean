import Mathlib
/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix

/-- A primitive 12-th root of unity. -/

lemma comm_key : C12 * V12 = V12 * Matrix.diagonal hval := by
  ext i k
  have hu : (om ^ (k : ℕ)) ^ 12 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, om_pow_twelve, one_pow]
  have hinv : (om ^ (k : ℕ))⁻¹ = (om ^ (k : ℕ)) ^ 11 :=
    inv_eq_of_mul_eq_one_right (by linear_combination hu)
  rw [Matrix.mul_apply, Matrix.mul_diagonal, hval_eq, hinv, V12_apply]
  simp only [V12_apply]
  exact sum_C12_pow i _ hu

