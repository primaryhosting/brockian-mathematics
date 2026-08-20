/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
noncomputable def chains (α : Type*) [Fintype α] [PartialOrder α] : Finset (Finset α) :=
  Finset.univ.filter fun s : Finset α => IsChain (· ≤ ·) (s : Set α)

/-- The length of a longest chain in a finite partial order. -/
noncomputable def longestChain (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  (chains α).sup Finset.card

/-- The set of sizes of antichain covers: `n` belongs to it when the elements can be
coloured with colours `< n` so that each colour class is an antichain. -/
def antichainCovers (α : Type*) [PartialOrder α] : Set ℕ :=
  {n : ℕ | ∃ f : α → ℕ, (∀ a : α, f a < n) ∧ ∀ a b : α, f a = f b → a ≤ b → a = b}

lemma mem_chains {s : Finset α} : s ∈ chains α ↔ IsChain (· ≤ ·) (s : Set α) := by
  simp [chains]

lemma chains_nonempty : (chains α).Nonempty :=
  ⟨∅, by simp [mem_chains, IsChain, Set.Pairwise]⟩

lemma card_le_longestChain {s : Finset α} (hs : IsChain (· ≤ ·) (s : Set α)) :
    s.card ≤ longestChain α :=
  Finset.le_sup (f := Finset.card) (mem_chains.mpr hs)

/-- The height of an element: the size of a longest chain all of whose elements are `≤ a`. -/
noncomputable def height (a : α) : ℕ :=
  ((chains α).filter fun s => ∀ x ∈ s, x ≤ a).sup Finset.card

lemma height_le_longestChain (a : α) : height a ≤ longestChain α :=
  Finset.sup_mono (Finset.filter_subset _ _)

lemma exists_height_chain (a : α) :
    ∃ s : Finset α, IsChain (· ≤ ·) (s : Set α) ∧ (∀ x ∈ s, x ≤ a) ∧ s.card = height a := by
  have hne : ((chains α).filter fun s => ∀ x ∈ s, x ≤ a).Nonempty :=
    ⟨{a}, by simp [mem_chains, IsChain, Set.Pairwise]⟩
  obtain ⟨s, hs, hcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, mem_chains] at hs
  exact ⟨s, hs.1, hs.2, hcard.symm⟩

lemma one_le_height (a : α) : 1 ≤ height a := by
  have : ({a} : Finset α) ∈ (chains α).filter fun s => ∀ x ∈ s, x ≤ a := by
    simp [mem_chains, IsChain, Set.Pairwise]
  have h := Finset.le_sup (f := Finset.card) this
  rw [Finset.card_singleton] at h
  exact h

lemma height_lt_height_of_lt {a b : α} (hab : a < b) : height a < height b := by
  obtain ⟨s, hchain, hle, hcard⟩ := exists_height_chain a
  have hb : b ∉ s := fun hb => absurd (lt_of_lt_of_le hab (hle b hb)) (lt_irrefl a)
  have hchain' : IsChain (· ≤ ·) ((insert b s : Finset α) : Set α) := by
    rw [Finset.coe_insert]
    refine hchain.insert ?_
    intro x hx _
    exact Or.inr (le_of_lt (lt_of_le_of_lt (hle x (by simpa using hx)) hab))
  have hmem : (insert b s : Finset α) ∈ (chains α).filter fun t => ∀ x ∈ t, x ≤ b := by
    refine Finset.mem_filter.mpr ⟨mem_chains.mpr hchain', ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · exact h ▸ le_refl b
    · exact le_of_lt (lt_of_le_of_lt (hle x h) hab)
  have := Finset.le_sup (f := Finset.card) hmem
  rw [Finset.card_insert_of_notMem hb, hcard] at this
  have hb2 : height a + 1 ≤ height b := this
  omega

/-- **Mirsky's theorem** (the dual form of Dilworth's theorem): in a finite partial order,
the minimum number of antichains needed to cover the poset equals the size of a longest
chain. -/
theorem dilworth (α : Type*) [Fintype α] [PartialOrder α] :
    IsLeast (antichainCovers α) (longestChain α) := by
  constructor
  · -- the height function is a colouring with `longestChain α` colours
    refine ⟨fun a => height a - 1, ?_, ?_⟩
    · intro a
      show height a - 1 < longestChain α
      have h1 := one_le_height a
      have h2 := height_le_longestChain a
      omega
    · intro a b hf hab
      have hf' : height a - 1 = height b - 1 := hf
      rcases eq_or_lt_of_le hab with h | h
      · exact h
      · have := height_lt_height_of_lt h
        have h1 := one_le_height a
        have h2 := one_le_height b
        omega
  · -- any antichain cover has at least as many parts as a longest chain
    rintro n ⟨f, hlt, hanti⟩
    obtain ⟨s, hs, hcard⟩ := Finset.exists_mem_eq_sup (chains α) chains_nonempty Finset.card
    rw [mem_chains] at hs
    have hinj : Set.InjOn f (s : Set α) := by
      intro x hx y hy hxy
      rcases eq_or_ne x y with h | h
      · exact h
      · rcases hs hx hy h with hle | hle
        · exact hanti x y hxy hle
        · exact (hanti y x hxy.symm hle).symm
    have himg : (s.image f) ⊆ Finset.range n := by
      intro m hm
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_range.mpr (hlt x)
    have : s.card = (s.image f).card := (Finset.card_image_of_injOn hinj).symm
    calc longestChain α = s.card := by rw [longestChain, hcard]
      _ = (s.image f).card := this
      _ ≤ (Finset.range n).card := Finset.card_le_card himg
      _ = n := Finset.card_range n

end Math

