import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The real quadratic form `x ↦ re ⟪x, M x⟫` associated to a matrix `M`. -/

lemma qform_le {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) {c : ℝ}
    (h : ∀ i, hM.eigenvalues i ≤ c) (x : EuclideanSpace ℂ (Fin d)) :
    qform M x ≤ c * ‖x‖ ^ 2 := by
  rw [qform_eq hM, ← hM.eigenvectorBasis.sum_sq_norm_inner_right x, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h2 : (0:ℝ) ≤ ‖inner ℂ (hM.eigenvectorBasis i) x‖ ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_right (h i) h2

/-- On the span of eigenvectors with nonpositive eigenvalues, the quadratic form is nonpositive. -/
