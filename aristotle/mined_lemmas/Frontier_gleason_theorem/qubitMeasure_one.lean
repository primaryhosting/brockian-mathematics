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

lemma qubitMeasure_one : qubitMeasure 1 = 1 := by
  unfold qubitMeasure; norm_num

/-- For a two-dimensional projection whose `(0,0)` entry has real part `1/2`, the
off-diagonal entry is nonzero. -/
