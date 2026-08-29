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

lemma proj_eq_one_of_eigenvalues_one {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsProj P)
    (h : ∀ j, hP.1.eigenvalues j = 1) : P = 1 := by
  conv_lhs => rw [hP.1.spectral_theorem]
  have hd : (Matrix.diagonal (RCLike.ofReal ∘ hP.1.eigenvalues) : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext j
    simp [h j]
  rw [hd, map_one]

