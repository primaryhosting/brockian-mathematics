import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-! ## Setup: Euclidean norm, contractions and the trace norm by duality -/

/-- The Euclidean (ℓ²) norm of a real vector indexed by `Fin n`. -/

lemma abs_dot_le {n : ℕ} (v w : Fin n → ℝ) :
    |∑ i, v i * w i| ≤ nrm v * nrm w := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w
  have h2 : (∑ i, v i * w i) ^ 2 ≤ (nrm v * nrm w) ^ 2 := by
    rw [mul_pow, nrm_sq, nrm_sq]; exact h
  calc |∑ i, v i * w i| = Real.sqrt ((∑ i, v i * w i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((nrm v * nrm w) ^ 2) := Real.sqrt_le_sqrt h2
    _ = nrm v * nrm w := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg (nrm_nonneg _) (nrm_nonneg _))]

