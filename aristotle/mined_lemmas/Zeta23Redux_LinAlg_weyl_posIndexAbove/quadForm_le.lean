import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The quadratic form `x ↦ Re ⟪x, A x⟫` attached to a complex matrix `A`,
seen as an operator on `EuclideanSpace ℂ (Fin d)`. -/

lemma quadForm_le {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (t : ℝ)
    (h : ∀ i, hA.eigenvalues i ≤ t) (x : EuclideanSpace ℂ (Fin d)) :
    quadForm A x ≤ t * ‖x‖ ^ 2 := by
  rw [quadForm_eq hA, ← hA.eigenvectorBasis.sum_sq_norm_inner_right x, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (h j) (by positivity)

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/
