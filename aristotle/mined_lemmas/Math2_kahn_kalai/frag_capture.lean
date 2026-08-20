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
Covers, costs, and minimum fragments (Park–Pham).
-/
import Mathlib
import RequestProject.KahnKalai.Measure

open Finset
open scoped Classical

namespace Math2

variable {α : Type*} [DecidableEq α]

/-! ## Covers and their costs -/

/-- `G` is a cover of `H`: every member of `H` contains a member of `G`. -/

lemma frag_capture {H : Finset (Finset α)} {S : Finset α} (hS : S ∈ H) (W : Finset α) :
    ∃ S' ∈ H, S' ⊆ W ∪ frag H S W := by
  obtain ⟨S', hS', hEq⟩ := Finset.mem_image.mp (frag_mem hS W)
  rw [Finset.mem_filter] at hS'
  refine ⟨S', hS'.1, ?_⟩
  intro x hx
  by_cases hxW : x ∈ W
  · exact Finset.mem_union_left _ hxW
  · exact Finset.mem_union_right _ (by rw [← hEq]; exact Finset.mem_sdiff.mpr ⟨hx, hxW⟩)

/-- Minimality: any edge of `H` inside `W ∪ frag H S W` contains the fragment. -/
