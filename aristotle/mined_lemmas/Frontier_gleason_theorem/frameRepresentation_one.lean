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

theorem frameRepresentation_one : FrameRepresentation 1 := by
  intro mu hmu
  refine ⟨1, Matrix.isHermitian_one, fun v hv => ?_⟩
  have hv2 : star v ⬝ᵥ v = 1 := hv
  have hv' : (starRingEnd ℂ) (v 0) * v 0 = 1 := by
    simpa [dotProduct, Fin.sum_univ_one] using hv2
  have h1 : rankOneProj v = 1 := by
    ext i j
    fin_cases i; fin_cases j
    simp only [rankOneProj, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def,
      Matrix.one_apply_eq]
    rw [mul_comm]
    exact hv'
  rw [h1, one_mul, hmu.normalized, Matrix.trace_one]
  simp

/-- Unconditional Gleason theorem in dimension one. -/
