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

lemma proj_exists_eigenvalue_one {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsProj P)
    (h : P ≠ 0) : ∃ j, hP.1.eigenvalues j = 1 := by
  by_contra hc
  push_neg at hc
  refine h (hP.1.eigenvalues_eq_zero_iff.mp ?_)
  funext j
  rcases proj_eigenvalues_eq_zero_or_one hP j with hj | hj
  · simpa using hj
  · exact absurd hj (hc j)

