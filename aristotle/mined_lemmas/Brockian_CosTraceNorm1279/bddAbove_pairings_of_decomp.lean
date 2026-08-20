import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-! ## Setup: Euclidean norm, contractions and the trace norm by duality -/

/-- The Euclidean (ℓ²) norm of a real vector indexed by `Fin n`. -/

lemma bddAbove_pairings_of_decomp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (a b c d : Fin n → ℝ)
    (hA : A = Matrix.of fun i j => a i * b j + c i * d j) : BddAbove (pairings A) := by
  refine ⟨nrm a * nrm b + nrm c * nrm d, ?_⟩
  rintro t ⟨B, hB, rfl⟩
  subst hA
  exact (le_abs_self _).trans (abs_trace_le_of_decomp a b c d B hB)

/-- Trace-norm bound for a matrix presented as a sum of two rank-one matrices. -/
