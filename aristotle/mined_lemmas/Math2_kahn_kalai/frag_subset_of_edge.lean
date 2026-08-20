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

lemma frag_subset_of_edge {H : Finset (Finset α)} {S : Finset α} (hS : S ∈ H) (W : Finset α)
    {Sh : Finset α} (hSh : Sh ∈ H) (hsub : Sh ⊆ W ∪ frag H S W) : frag H S W ⊆ Sh := by
  have hfragS : frag H S W ⊆ S := frag_subset hS W
  have hcand : Sh \ W ∈ cands H S W := by
    refine Finset.mem_image.mpr ⟨Sh, Finset.mem_filter.mpr ⟨hSh, ?_⟩, rfl⟩
    intro x hx
    rcases Finset.mem_union.mp (hsub hx) with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (hfragS h)
  have hle : (frag H S W).card ≤ (Sh \ W).card := frag_min hS W _ hcand
  have hsub2 : Sh \ W ⊆ frag H S W := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rcases Finset.mem_union.mp (hsub hx.1) with h | h
    · exact absurd h hx.2
    · exact h
  have : Sh \ W = frag H S W := Finset.eq_of_subset_of_card_le hsub2 hle
  rw [← this]
  exact Finset.sdiff_subset

/-! ## One step of the iteration -/

/-- The cover produced at one step: the minimum fragments that are too big. -/
