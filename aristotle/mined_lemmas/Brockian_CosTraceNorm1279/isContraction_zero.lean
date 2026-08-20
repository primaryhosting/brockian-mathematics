import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-! ## Setup: Euclidean norm, contractions and the trace norm by duality -/

/-- The Euclidean (ℓ²) norm of a real vector indexed by `Fin n`. -/

lemma isContraction_zero {n : ℕ} : IsContraction (0 : Matrix (Fin n) (Fin n) ℝ) := by
  intro v
  rw [Matrix.zero_mulVec]
  simp [nrm]

