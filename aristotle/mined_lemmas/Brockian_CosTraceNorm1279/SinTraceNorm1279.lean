import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-! ## Setup: Euclidean norm, contractions and the trace norm by duality -/

/-- The Euclidean (ℓ²) norm of a real vector indexed by `Fin n`. -/

theorem SinTraceNorm1279 {n : ℕ} (x y : Fin n → ℝ) :
    traceNorm (sinMatrix x y) ≤ n := by
  refine le_trans (traceNorm_le_of_decomp _ (fun i => Real.sin (x i)) (fun j => Real.cos (y j))
    (fun i => Real.cos (x i)) (fun j => -Real.sin (y j)) ?_) ?_
  · ext i j
    simp [sinMatrix, Real.sin_sub]
    ring
  · rw [show (fun j => -Real.sin (y j)) = (fun j => -((fun j => Real.sin (y j)) j)) from rfl,
      nrm_neg]
    exact four_norm_bound _ _ _ _
      (by rw [add_comm]; exact nrm_cos_sq_add_nrm_sin_sq x) (nrm_cos_sq_add_nrm_sin_sq y)

/-- The analogous bound for the matrix `cos (x i + y j)`. -/
