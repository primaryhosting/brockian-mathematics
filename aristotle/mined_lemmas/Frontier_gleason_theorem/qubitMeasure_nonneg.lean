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

lemma qubitMeasure_nonneg (P : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ qubitMeasure P := by
  unfold qubitMeasure
  split_ifs
  · norm_num
  · norm_num
  · exact tieBreak_nonneg _

