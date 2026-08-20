import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-! ## Setup: Euclidean norm, contractions and the trace norm by duality -/

/-- The Euclidean (ℓ²) norm of a real vector indexed by `Fin n`. -/

lemma nrm_neg {n : ℕ} (v : Fin n → ℝ) : (nrm fun i => -(v i)) = nrm v := by
  simp [nrm]

