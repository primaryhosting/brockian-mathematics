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

lemma dotProduct_mulVec_smul (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    star (c • x) ⬝ᵥ (M *ᵥ (c • x)) = (star c * c) * (star x ⬝ᵥ (M *ᵥ x)) := by
  simp only [Matrix.mulVec_smul, star_smul, dotProduct, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

