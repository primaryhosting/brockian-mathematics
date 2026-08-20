import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-! ## Setup: Euclidean norm, contractions and the trace norm by duality -/

/-- The Euclidean (ℓ²) norm of a real vector indexed by `Fin n`. -/

lemma nrm_sq {n : ℕ} (v : Fin n → ℝ) : (nrm v) ^ 2 = ∑ i, (v i) ^ 2 := by
  apply Real.sq_sqrt; positivity

