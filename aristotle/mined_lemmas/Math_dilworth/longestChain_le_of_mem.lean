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

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The finset of all chains (as finsets) of a finite partial order. -/

lemma longestChain_le_of_mem {n : ℕ} (hn : n ∈ antichainCoverCards α) :
    longestChain α ≤ n := by
  obtain ⟨C, hcard, hanti, hcover⟩ := hn
  obtain ⟨K, hK, hKsup⟩ :=
    Finset.exists_mem_eq_sup (allChains α) ⟨∅, by rw [mem_allChains]; simp⟩ Finset.card
  rw [mem_allChains] at hK
  choose g hg hxg using hcover
  have hinj : Set.InjOn g (K : Set α) := by
    intro a ha b hb hab
    by_contra hne
    have hA : IsAntichain (· ≤ ·) ((g a : Finset α) : Set α) := hanti _ (hg a)
    have hbmem : b ∈ (g a : Finset α) := by rw [hab]; exact hxg b
    rcases hK ha hb hne with h | h
    · exact hA (by exact_mod_cast hxg a) (by exact_mod_cast hbmem) hne h
    · exact hA (by exact_mod_cast hbmem) (by exact_mod_cast hxg a) (Ne.symm hne) h
  have : K.card ≤ C.card := by
    refine Finset.card_le_card_of_injOn g (fun a ha => hg a) ?_
    intro a ha b hb hab
    exact hinj (by simpa using ha) (by simpa using hb) hab
  rw [longestChain, hKsup, ← hcard]
  exact this

/-- **Mirsky's theorem** (dual of Dilworth's theorem): in a finite partial order, the minimum
number of antichains needed to cover the order equals the length of a longest chain. -/
