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

noncomputable def tieBreak (z : ℂ) : ℝ :=
  if 0 < z.re then 1 else if z.re < 0 then 0 else if 0 < z.im then 1 else 0

