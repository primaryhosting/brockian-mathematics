import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib
/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace
open Matrix

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/

lemma qform_le_of_eigenvalues_le {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) {θ : ℝ}
    (hle : ∀ i, hM.eigenvalues i ≤ θ) (x : EuclideanSpace ℂ (Fin d)) :
    qform M x ≤ θ * ‖x‖ ^ 2 := by
  rw [qform_eq_sum hM, ← hM.eigenvectorBasis.sum_sq_norm_inner_right x, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hle i) (by positivity)

/-- If `x` is orthogonal to all eigenvectors with positive eigenvalue, the quadratic form
is nonpositive. -/
