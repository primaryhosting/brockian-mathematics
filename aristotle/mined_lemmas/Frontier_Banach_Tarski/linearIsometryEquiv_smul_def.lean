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

@[simp] lemma linearIsometryEquiv_smul_def {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (g : E ≃ₗᵢ[ℝ] E) (x : E) : g • x = g x := rfl

variable {X : Type*} (G : Type*) [Group G] [MulAction G X]

/-- Two sets `A B : Set X` are *equidecomposable* with respect to a group `G` acting on `X`
if there is a bijection `A → B` which is obtained by cutting `A` into finitely many pieces
and moving each piece by a single element of `G`.  This is expressed by requiring a bijection
`f : A → B` and a *finite* set `S` of group elements such that every point of `A` is moved by
some element of `S`. -/
