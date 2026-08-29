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

lemma rankOneProj_mul (v w : Fin n → ℂ) :
    rankOneProj v * rankOneProj w = (star v ⬝ᵥ w) • Matrix.vecMulVec v (star w) := by
  ext i j
  simp only [rankOneProj, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
    dotProduct, Pi.star_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

