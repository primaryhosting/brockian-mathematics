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

namespace Math

variable {α : Type*} [PartialOrder α] [Fintype α]

/-- The finset of all chains of a finite partial order. -/

lemma longestChain_le_card_of_cover {S : Finset (Finset α)} (h : IsAntichainCover S) :
    longestChain α ≤ S.card := by
  obtain ⟨C, hC, hCcard⟩ := exists_longest_chain (α := α)
  rw [mem_chainsFinset] at hC
  choose f hfS hfmem using h.2
  have hinj : Set.InjOn f (C : Set α) := by
    intro a ha b hb hfab
    by_contra hab
    have hcomp := hC ha hb hab
    have hA : IsAntichain (· ≤ ·) ((f a : Finset α) : Set α) := h.1 _ (hfS a)
    have hbmem : b ∈ (f a : Finset α) := by rw [hfab]; exact hfmem b
    rcases hcomp with hle | hle
    · exact hA (by exact_mod_cast hfmem a) (by exact_mod_cast hbmem) hab hle
    · exact hA (by exact_mod_cast hbmem) (by exact_mod_cast hfmem a) (Ne.symm hab) hle
  have : C.card ≤ S.card := by
    refine Finset.card_le_card_of_injOn f (fun a ha => hfS a) ?_
    intro a ha b hb hfab
    exact hinj (by exact_mod_cast ha) (by exact_mod_cast hb) hfab
  omega

/-- **Mirsky's theorem**: in a finite poset, the minimum number of antichains needed to
cover the poset equals the number of elements of a longest chain. -/
