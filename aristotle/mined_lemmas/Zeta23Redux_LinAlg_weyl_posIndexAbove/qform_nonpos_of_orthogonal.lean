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

lemma qform_nonpos_of_orthogonal {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian)
    {x : EuclideanSpace ℂ (Fin d)}
    (hx : ∀ i, 0 < hM.eigenvalues i → ⟪hM.eigenvectorBasis i, x⟫_ℂ = 0) :
    qform M x ≤ 0 := by
  rw [qform_eq_sum hM]
  refine Finset.sum_nonpos fun i _ => ?_
  rcases lt_or_ge 0 (hM.eigenvalues i) with h | h
  · rw [hx i h]
    simp
  · exact mul_nonpos_of_nonpos_of_nonneg h (by positivity)

/-- If every eigenvector component of a nonzero `x` corresponds to an eigenvalue above `θ`,
then the quadratic form is strictly above `θ‖x‖²`. -/
