import Mathlib
/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Frontier

open Matrix

variable {n : ℕ}

/-! ## Basic notions -/

/-- The rank-one (orthogonal) projection onto the line spanned by a unit vector `v`,
written as the matrix `v vᴴ`. -/

lemma trace2_eq_sum_eigenvalues {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P.IsHermitian) :
    P.trace = ((hP.eigenvalues 0 + hP.eigenvalues 1 : ℝ) : ℂ) := by
  rw [hP.trace_eq_sum_eigenvalues, Fin.sum_univ_two]
  norm_cast

/-- In dimension two, two nonzero orthogonal projections must be complementary. -/
