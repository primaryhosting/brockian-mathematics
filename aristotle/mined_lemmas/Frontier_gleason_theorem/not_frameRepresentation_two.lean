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

theorem not_frameRepresentation_two : ¬ FrameRepresentation 2 := fun h =>
  not_exists_density_for_qubitMeasure
    (gleason_of_frameRepresentation h qubitMeasure isQuantumMeasure_qubitMeasure)

/-- **The dimension hypothesis in Gleason's theorem is necessary**: in dimension two there is a
quantum measure that does not come from any density operator. -/
