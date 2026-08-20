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

lemma norm_sq_eq_sum_repr (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)))
    (x : EuclideanSpace ℂ (Fin d)) : ‖x‖ ^ 2 = ∑ j, ‖b.repr x j‖ ^ 2 := by
  rw [← b.repr.norm_map x, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

section

variable {M : Matrix (Fin d) (Fin d) ℂ}

