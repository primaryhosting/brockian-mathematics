/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- A colouring of the poset by `{0, …, n-1}` whose colour classes are antichains. -/
def IsAntichainColoring (n : ℕ) (f : α → ℕ) : Prop :=
  (∀ x, f x < n) ∧ ∀ x y : α, f x = f y → x ≤ y → x = y

/-- The minimum number of antichains needed to cover the poset. -/
noncomputable def minAntichainCover (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  sInf {n : ℕ | ∃ f : α → ℕ, IsAntichainColoring n f}

/-- The finset of all chains of the poset. -/
noncomputable def chains (α : Type*) [Fintype α] [PartialOrder α] : Finset (Finset α) :=
  (Finset.univ : Finset (Finset α)).filter (fun C => IsChain (· ≤ ·) (C : Set α))

/-- The number of elements in a longest chain of the poset. -/
noncomputable def longestChain (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  (chains α).sup Finset.card

/-- The "height" of `x`: the size of a longest chain with maximum element `x`. -/
noncomputable def height' (x : α) : ℕ :=
  ((chains α).filter (fun C => x ∈ C ∧ ∀ z ∈ C, z ≤ x)).sup Finset.card

lemma mem_chains {C : Finset α} : C ∈ chains α ↔ IsChain (· ≤ ·) (C : Set α) := by
  simp [chains]

lemma card_le_longestChain {C : Finset α} (hC : IsChain (· ≤ ·) (C : Set α)) :
    C.card ≤ longestChain α :=
  Finset.le_sup (f := Finset.card) (mem_chains.mpr hC)

lemma exists_chain_card_eq : ∃ C : Finset α, IsChain (· ≤ ·) (C : Set α) ∧
    C.card = longestChain α := by
  have hne : (chains α).Nonempty := ⟨∅, by simp [mem_chains]⟩
  obtain ⟨C, hC, hcard⟩ := Finset.exists_mem_eq_sup (chains α) hne Finset.card
  exact ⟨C, mem_chains.mp hC, hcard.symm⟩

lemma one_le_height' (x : α) : 1 ≤ height' x := by
  have h : ({x} : Finset α) ∈ (chains α).filter (fun C => x ∈ C ∧ ∀ z ∈ C, z ≤ x) := by
    simp [chains, IsChain, Set.Pairwise]
  have h2 : ({x} : Finset α).card ≤ height' x := Finset.le_sup (f := Finset.card) h
  simpa using h2

lemma height'_le (x : α) : height' x ≤ longestChain α := by
  refine Finset.sup_le ?_
  intro C hC
  exact card_le_longestChain (mem_chains.mp (Finset.mem_filter.mp hC).1)

lemma exists_chain_height' (x : α) : ∃ C : Finset α, IsChain (· ≤ ·) (C : Set α) ∧ x ∈ C ∧
    (∀ z ∈ C, z ≤ x) ∧ C.card = height' x := by
  have hne : ((chains α).filter (fun C => x ∈ C ∧ ∀ z ∈ C, z ≤ x)).Nonempty := by
    refine ⟨{x}, ?_⟩
    simp [chains, IsChain, Set.Pairwise]
  obtain ⟨C, hC, hcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter] at hC
  exact ⟨C, mem_chains.mp hC.1, hC.2.1, hC.2.2, hcard.symm⟩

lemma height'_strictMono {x y : α} (hxy : x < y) : height' x < height' y := by
  obtain ⟨C, hC, hxC, hle, hcard⟩ := exists_chain_height' x
  have hyC : y ∉ C := by
    intro hy
    exact absurd (lt_of_lt_of_le hxy (hle y hy)) (lt_irrefl x)
  have hchain : IsChain (· ≤ ·) ((insert y C : Finset α) : Set α) := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact Or.inr (le_trans (hle b hb) hxy.le)
    · rcases hb with rfl | hb
      · exact Or.inl (le_trans (hle a ha) hxy.le)
      · exact hC ha hb hab
  have hmem : (insert y C : Finset α) ∈
      (chains α).filter (fun C => y ∈ C ∧ ∀ z ∈ C, z ≤ y) := by
    refine Finset.mem_filter.mpr ⟨mem_chains.mpr hchain, Finset.mem_insert_self _ _, ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact le_rfl
    · exact le_trans (hle z hz) hxy.le
  have hle2 : (insert y C).card ≤ height' y := Finset.le_sup (f := Finset.card) hmem
  rw [Finset.card_insert_of_notMem hyC, hcard] at hle2
  omega

lemma coverable_longestChain :
    ∃ f : α → ℕ, IsAntichainColoring (longestChain α) f := by
  refine ⟨fun x => height' x - 1, ?_, ?_⟩
  · intro x
    show height' x - 1 < longestChain α
    have h1 := one_le_height' x
    have h2 := height'_le x
    omega
  · intro x y hxy hle
    have hxy' : height' x - 1 = height' y - 1 := hxy
    by_contra hne
    have hlt : x < y := lt_of_le_of_ne hle hne
    have h3 := height'_strictMono hlt
    have h1 := one_le_height' x
    have h2 := one_le_height' y
    omega

lemma longestChain_le_of_coloring {n : ℕ} {f : α → ℕ} (hf : IsAntichainColoring n f) :
    longestChain α ≤ n := by
  obtain ⟨C, hC, hcard⟩ := exists_chain_card_eq (α := α)
  have hinj : Set.InjOn f (C : Set α) := by
    intro a ha b hb hab
    by_cases h : a = b
    · exact h
    · rcases hC ha hb h with h1 | h1
      · exact hf.2 a b hab h1
      · exact (hf.2 b a hab.symm h1).symm
  have hmap : Set.MapsTo f (C : Set α) ((Finset.range n : Finset ℕ) : Set ℕ) := by
    intro a _
    simpa using hf.1 a
  have := Finset.card_le_card_of_injOn f hmap hinj
  simpa [hcard] using this

/-- **Mirsky's theorem** (the dual of Dilworth's theorem): in a finite poset, the minimum
number of antichains needed to cover the poset equals the number of elements of a longest
chain. -/
theorem dilworth (α : Type*) [Fintype α] [PartialOrder α] :
    minAntichainCover α = longestChain α := by
  have hmem : longestChain α ∈ {n : ℕ | ∃ f : α → ℕ, IsAntichainColoring n f} :=
    coverable_longestChain
  refine le_antisymm (Nat.sInf_le hmem) ?_
  have hne : {n : ℕ | ∃ f : α → ℕ, IsAntichainColoring n f}.Nonempty := ⟨_, hmem⟩
  obtain ⟨f, hf⟩ := Nat.sInf_mem hne
  exact longestChain_le_of_coloring hf

/-- Sanity check: the two-element chain `Fin 2` has longest chain of size `2`, hence needs
two antichains to be covered. -/
example : minAntichainCover (Fin 2) = 2 := by
  rw [dilworth]
  refine le_antisymm (Finset.sup_le ?_) ?_
  · intro C _
    simpa using Finset.card_le_univ C
  · have hchain : IsChain (· ≤ ·) ((Finset.univ : Finset (Fin 2)) : Set (Fin 2)) := by
      intro a _ b _ _
      rcases le_total a b with h | h
      · exact Or.inl h
      · exact Or.inr h
    simpa using card_le_longestChain hchain

end Math

