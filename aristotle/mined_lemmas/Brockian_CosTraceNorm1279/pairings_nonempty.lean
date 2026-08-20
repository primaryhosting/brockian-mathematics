import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-! ## Setup: Euclidean norm, contractions and the trace norm by duality -/

/-- The Euclidean (ℓ²) norm of a real vector indexed by `Fin n`. -/

lemma pairings_nonempty {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : (pairings A).Nonempty :=
  ⟨Matrix.trace ((0 : Matrix (Fin n) (Fin n) ℝ) * A), 0, isContraction_zero, rfl⟩

/-! ## The dual pairing against a matrix of rank at most two -/

/-- The pairing of a contraction with a rank-≤2 matrix is bounded by the sum of the
products of the norms of the factors. -/
