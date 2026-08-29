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

lemma PowA_disjoint_St {p : Fin 2 × Bool} (hp : p ≠ (0, false)) : Disjoint PowA (St p) := by
  rw [Set.disjoint_left]
  intro w hw hw'
  rw [mem_St] at hw'
  rcases PowA_head hw with h | h <;> rw [hw'] at h
  · simp at h
  · exact hp (Option.some_injective _ h)

/-- The four pieces cover the group. -/
