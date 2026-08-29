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

def CrossPreserving : Subgroup (E3 ≃ₗᵢ[ℝ] E3) where
  carrier := {g | ∀ u v : E3, g (cross3 u v) = cross3 (g u) (g v)}
  one_mem' := by intro u v; rfl
  mul_mem' := by
    intro f g hf hg u v
    show f (g (cross3 u v)) = cross3 (f (g u)) (f (g v))
    rw [hg u v, hf (g u) (g v)]
  inv_mem' := by
    intro g hg u v
    apply (g : E3 ≃ₗᵢ[ℝ] E3).injective
    show g (g⁻¹ (cross3 u v)) = g (cross3 (g⁻¹ u) (g⁻¹ v))
    rw [hg (g⁻¹ u) (g⁻¹ v)]
    show (g * g⁻¹) (cross3 u v) = cross3 ((g * g⁻¹) u) ((g * g⁻¹) v)
    rw [mul_inv_cancel]
    rfl

