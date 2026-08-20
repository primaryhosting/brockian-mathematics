import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-! ## Setup: Euclidean norm, contractions and the trace norm by duality -/

/-- The Euclidean (ℓ²) norm of a real vector indexed by `Fin n`. -/

theorem CosSumTraceNorm1279 {n : ℕ} (x y : Fin n → ℝ) :
    traceNorm (cosSumMatrix x y) ≤ n := by
  refine le_trans (traceNorm_le_of_decomp _ (fun i => Real.cos (x i)) (fun j => Real.cos (y j))
    (fun i => Real.sin (x i)) (fun j => -Real.sin (y j)) ?_) ?_
  · ext i j
    simp [cosSumMatrix, Real.cos_add]
    ring
  · rw [show (fun j => -Real.sin (y j)) = (fun j => -((fun j => Real.sin (y j)) j)) from rfl,
      nrm_neg]
    exact four_norm_bound _ _ _ _ (nrm_cos_sq_add_nrm_sin_sq x) (nrm_cos_sq_add_nrm_sin_sq y)

/-! ## Sharpness -/

/-- The scaled all-ones matrix `(1/n) J` is a contraction. -/
