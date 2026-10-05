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

lemma proj_eigenvalues_nonneg {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsProj P) (j : Fin n) :
    0 ≤ hP.1.eigenvalues j := by
  rcases proj_eigenvalues_eq_zero_or_one hP j with h | h <;> simp [h]

