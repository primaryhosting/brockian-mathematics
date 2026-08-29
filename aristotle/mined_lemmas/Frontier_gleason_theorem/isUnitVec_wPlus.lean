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

lemma isUnitVec_wPlus : IsUnitVec wPlus := by
  show star wPlus ⬝ᵥ wPlus = 1
  norm_num [wPlus, dotProduct, Fin.sum_univ_two, Complex.ext_iff, map_div₀, map_ofNat]

