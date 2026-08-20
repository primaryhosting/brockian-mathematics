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

lemma isCover_step {G H : Finset (Finset α)} {b : ℕ} {W : Finset α}
    (hG : IsCover G (Hnext H b W)) : IsCover (G ∪ Ucov H b W) H := by
  intro S hS
  by_cases hbig : b < (frag H S W).card
  · refine ⟨frag H S W, ?_, frag_subset hS W⟩
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨hS, hbig⟩, rfl⟩)
  · have hmem : frag H S W ∈ Hnext H b W :=
      Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨hS, not_lt.mp hbig⟩, rfl⟩
    obtain ⟨T, hT, hTsub⟩ := hG _ hmem
    exact ⟨T, Finset.mem_union_left _ hT, hTsub.trans (frag_subset hS W)⟩

/-- Cost recursion: the minimal cover cost of `H` is at most the cost of the step cover plus
the minimal cover cost of the next hypergraph. -/
