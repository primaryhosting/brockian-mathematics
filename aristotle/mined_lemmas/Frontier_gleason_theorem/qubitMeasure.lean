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

noncomputable def qubitMeasure (P : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  if 1 / 2 < (P 0 0).re then 1 else if (P 0 0).re < 1 / 2 then 0 else tieBreak (P 0 1)

