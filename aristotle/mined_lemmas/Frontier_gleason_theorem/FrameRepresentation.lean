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

def FrameRepresentation (n : ℕ) : Prop :=
  ∀ mu : Matrix (Fin n) (Fin n) ℂ → ℝ, IsQuantumMeasure mu →
    ∃ rho : Matrix (Fin n) (Fin n) ℂ, rho.IsHermitian ∧
      ∀ v : Fin n → ℂ, IsUnitVec v →
        ((mu (rankOneProj v) : ℝ) : ℂ) = (rho * rankOneProj v).trace

/-! ## Rank-one projections -/

