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
# Rotations of three dimensional Euclidean space

Explicit rotations about the `z`- and `x`-axes, the cross product, and the fact that a
nontrivial rotation fixes at most two points of the unit sphere.
-/

open scoped RealInnerProductSpace

namespace BT

/-- Three dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- A vector of `E3` given by its three coordinates. -/

noncomputable def rotZequiv (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearEquiv.isometryOfInner
    { toLinearMap := rotZlin c s
      invFun := rotZlin c (-s)
      left_inv := by
        intro v
        refine ext3 ?_ ?_ rfl
        · simp; linear_combination (v 0) * h
        · simp; linear_combination (v 1) * h
      right_inv := by
        intro v
        refine ext3 ?_ ?_ rfl
        · simp; linear_combination (v 0) * h
        · simp; linear_combination (v 1) * h }
    (by
      intro u v
      rw [inner3, inner3]
      simp only [rotZlin_apply, vec3_zero, vec3_one, vec3_two, LinearEquiv.coe_mk]
      linear_combination (u 0 * v 0 + u 1 * v 1) * h)

/-- The rotation of the `yz`-plane as a linear isometry equivalence. -/
