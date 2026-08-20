import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-! ## Setup: Euclidean norm, contractions and the trace norm by duality -/

/-- The Euclidean (ℓ²) norm of a real vector indexed by `Fin n`. -/

def pairings {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  {t : ℝ | ∃ B : Matrix (Fin n) (Fin n) ℝ, IsContraction B ∧ Matrix.trace (B * A) = t}

/-- The trace norm (nuclear norm, Schatten 1-norm) of a real square matrix, defined by
duality: the supremum of `tr (B * A)` over all contractions `B`. -/
