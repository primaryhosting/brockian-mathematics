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

@[simp] lemma isometryEquiv_smul_def {M : Type*} [PseudoEMetricSpace M] (g : M ≃ᵢ M) (x : M) :
    g • x = g x := rfl

/-- The group of linear isometry equivalences of a normed space acts on the space. -/
instance linearIsometryEquivAction (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℝ E] :
    MulAction (E ≃ₗᵢ[ℝ] E) E where
  smul g x := g x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

