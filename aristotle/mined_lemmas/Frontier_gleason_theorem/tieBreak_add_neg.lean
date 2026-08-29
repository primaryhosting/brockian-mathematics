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

lemma tieBreak_add_neg {z : ℂ} (hz : z ≠ 0) : tieBreak z + tieBreak (-z) = 1 := by
  unfold tieBreak
  simp only [Complex.neg_re, Complex.neg_im]
  split_ifs <;>
    first
      | linarith
      | exact absurd (Complex.ext (show z.re = 0 by linarith) (show z.im = 0 by linarith)) hz

/-- A quantum measure on the qubit that is not given by any density operator. -/
