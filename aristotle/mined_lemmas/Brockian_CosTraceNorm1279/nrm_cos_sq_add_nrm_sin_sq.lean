import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-! ## Setup: Euclidean norm, contractions and the trace norm by duality -/

/-- The Euclidean (ℓ²) norm of a real vector indexed by `Fin n`. -/

lemma nrm_cos_sq_add_nrm_sin_sq {n : ℕ} (x : Fin n → ℝ) :
    (nrm fun i => Real.cos (x i)) ^ 2 + (nrm fun i => Real.sin (x i)) ^ 2 = n := by
  rw [nrm_sq, nrm_sq, ← Finset.sum_add_distrib]
  simp [Real.cos_sq_add_sin_sq]

