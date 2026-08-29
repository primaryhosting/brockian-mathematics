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

theorem gleason_dim_one (mu : Matrix (Fin 1) (Fin 1) ℂ → ℝ) (hmu : IsQuantumMeasure mu) :
    ∃ rho : Matrix (Fin 1) (Fin 1) ℂ, IsDensityOperator rho ∧
      ∀ P : Matrix (Fin 1) (Fin 1) ℂ, IsProj P → ((mu P : ℝ) : ℂ) = (rho * P).trace :=
  gleason_of_frameRepresentation frameRepresentation_one mu hmu

end Frontier

import RequestProject.Gleason
/-!
# Failure of Gleason's theorem in dimension two

Gleason's theorem needs `dim ≥ 3`.  Here we build, in dimension two, an explicit quantum
measure that does **not** come from a density operator.  Consequently
`Frontier.FrameRepresentation 2` is false, so the hypothesis of `Frontier.gleason_theorem`
genuinely encodes the dimension restriction.
-/

open scoped BigOperators
open scoped Classical
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Frontier

open Matrix

/-! ## Structure of projections in dimension two -/

