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

lemma Equidecomposable.map {H : Type*} [Group H] [MulAction H X] (φ : G →* H)
    (hφ : ∀ (g : G) (x : X), φ g • x = g • x) {A B : Set X} (h : Equidecomposable G A B) :
    Equidecomposable H A B := by
  classical
  obtain ⟨f, S, hbij, hS⟩ := h
  refine ⟨f, S.image φ, hbij, fun a ha => ?_⟩
  obtain ⟨g, hg, hga⟩ := hS a ha
  exact ⟨φ g, Finset.mem_image_of_mem _ hg, by rw [hφ]; exact hga⟩

