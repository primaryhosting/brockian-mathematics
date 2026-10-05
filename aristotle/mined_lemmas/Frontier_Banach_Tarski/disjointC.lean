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

lemma disjointC : Disjoint setC (gb • setD) := by
  rw [Set.disjoint_left]
  rintro w hw ⟨v, hv, rfl⟩
  rw [setD, mem_St] at hv
  obtain ⟨t, ht⟩ : ∃ t, v.toWord = ((1 : Fin 2), false) :: t := by
    cases hvw : v.toWord with
    | nil => rw [hvw] at hv; simp at hv
    | cons q t =>
        rw [hvw] at hv
        simp only [List.head?_cons, Option.some_inj] at hv
        exact ⟨t, by rw [hv]⟩
  have hmul : (gb • v).toWord = t := by
    rw [smul_eq_mul, gb_eq]
    exact toWord_letter_mul_cancel (p := ((1 : Fin 2), true)) (by simpa using ht)
  have hred : FreeGroup.IsReduced (((1 : Fin 2), false) :: t) := by
    rw [← ht]; exact FreeGroup.isReduced_toWord
  rw [setC, mem_St, hmul] at hw
  cases t with
  | nil => simp at hw
  | cons q t' =>
      simp only [List.head?_cons, Option.some_inj] at hw
      rw [FreeGroup.isReduced_cons_cons] at hred
      have := hred.1 (by rw [hw])
      simp [hw] at this

/-- **Paradoxical decomposition of the free group of rank two.** -/
