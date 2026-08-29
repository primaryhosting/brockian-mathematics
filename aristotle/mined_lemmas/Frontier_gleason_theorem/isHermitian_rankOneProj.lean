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

lemma isHermitian_rankOneProj (v : Fin n → ℂ) : (rankOneProj v).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, rankOneProj, Matrix.vecMulVec_apply, mul_comm]

