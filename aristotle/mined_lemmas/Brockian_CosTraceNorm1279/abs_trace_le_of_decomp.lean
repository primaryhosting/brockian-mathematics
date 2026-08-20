import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-! ## Setup: Euclidean norm, contractions and the trace norm by duality -/

/-- The Euclidean (ℓ²) norm of a real vector indexed by `Fin n`. -/

lemma abs_trace_le_of_decomp {n : ℕ} (a b c d : Fin n → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : IsContraction B) :
    |Matrix.trace (B * Matrix.of fun i j => a i * b j + c i * d j)| ≤
      nrm a * nrm b + nrm c * nrm d := by
  have hkey : Matrix.trace (B * Matrix.of fun i j => a i * b j + c i * d j)
      = (∑ i, b i * (B.mulVec a) i) + (∑ i, d i * (B.mulVec c) i) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply,
      Matrix.mulVec, dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hkey]
  refine (abs_add_le _ _).trans ?_
  gcongr ?_ + ?_
  · exact (abs_dot_le b (B.mulVec a)).trans (by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hB a) (nrm_nonneg b))
  · exact (abs_dot_le d (B.mulVec c)).trans (by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hB c) (nrm_nonneg d))

