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

lemma qf_eq_sum (hM : M.IsHermitian) (x : EuclideanSpace ℂ (Fin d)) :
    qf M x = ∑ j, hM.eigenvalues j * ‖hM.eigenvectorBasis.repr x j‖ ^ 2 := by
  rw [qf, ← hM.eigenvectorBasis.repr.inner_map_map x (Matrix.toLpLin 2 2 M x), PiLp.inner_apply,
    map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [repr_toLpLin hM x j]
  simp only [RCLike.inner_apply]
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring

/-- If all eigenvalues of a Hermitian matrix are at most `c`, its quadratic form is bounded by
`c * ‖x‖ ^ 2`. -/
