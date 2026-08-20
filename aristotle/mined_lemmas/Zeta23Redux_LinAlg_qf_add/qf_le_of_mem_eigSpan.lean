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

/-
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Redux.LinAlg

open Matrix Finset Module

variable {d : ℕ}

/-- The quadratic form `x ↦ Re ⟪x, M x⟫` associated with a matrix `M`, on `EuclideanSpace ℂ (Fin d)`.
-/

lemma qf_le_of_mem_eigSpan (hM : M.IsHermitian) {s : Finset (Fin d)} {c : ℝ}
    (hc : ∀ j ∈ s, hM.eigenvalues j ≤ c) {x : EuclideanSpace ℂ (Fin d)} (hx : x ∈ eigSpan hM s) :
    qf M x ≤ c * ‖x‖ ^ 2 := by
  have hzero : ∀ j ∉ s, hM.eigenvectorBasis.repr x j = 0 := fun j hj =>
    repr_eq_zero_of_mem_eigSpan hM hx hj
  rw [qf_eq_sum hM, norm_sq_eq_sum_repr hM.eigenvectorBasis x, Finset.mul_sum]
  have h1 : ∑ j, hM.eigenvalues j * ‖hM.eigenvectorBasis.repr x j‖ ^ 2
      = ∑ j ∈ s, hM.eigenvalues j * ‖hM.eigenvectorBasis.repr x j‖ ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ s) (fun j _ hj => by simp [hzero j hj])).symm
  have h2 : ∑ j, c * ‖hM.eigenvectorBasis.repr x j‖ ^ 2
      = ∑ j ∈ s, c * ‖hM.eigenvectorBasis.repr x j‖ ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ s) (fun j _ hj => by simp [hzero j hj])).symm
  rw [h1, h2]
  exact Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hc j hj) (by positivity)

/-- On the span of eigenvectors whose eigenvalues are strictly above `θ`, the quadratic form is
strictly above `θ * ‖x‖ ^ 2` for nonzero vectors. -/
