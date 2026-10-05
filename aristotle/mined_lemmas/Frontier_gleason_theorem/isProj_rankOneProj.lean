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

lemma isProj_rankOneProj {v : Fin n → ℂ} (hv : IsUnitVec v) : IsProj (rankOneProj v) := by
  refine ⟨isHermitian_rankOneProj v, ?_⟩
  rw [rankOneProj_mul, hv, one_smul]
  rfl

