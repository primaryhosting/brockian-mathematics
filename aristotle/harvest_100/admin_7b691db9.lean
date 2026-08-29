/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the required header is
-- reproduced verbatim as a module docstring immediately after the import below.)

import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

namespace Math

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The length of a longest chain in a finite poset. -/
noncomputable def longestChain (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  {s : Finset α | IsChain (· ≤ ·) (↑s : Set α)}.toFinset.sup Finset.card

/-- The set of possible sizes of antichain covers of a finite poset. -/
def antichainCoverSizes (α : Type*) [Fintype α] [PartialOrder α] : Set ℕ :=
  {n | ∃ C : Finset (Finset α), C.card ≤ n ∧
      (∀ s ∈ C, IsAntichain (· ≤ ·) (↑s : Set α)) ∧ ∀ x : α, ∃ s ∈ C, x ∈ s}

/-- The height of `x`: the largest size of a chain all of whose elements are `≤ x`. -/
noncomputable def height (x : α) : ℕ :=
  {s : Finset α | IsChain (· ≤ ·) (↑s : Set α) ∧ ∀ z ∈ s, z ≤ x}.toFinset.sup Finset.card

lemma chain_card_le_longestChain {s : Finset α} (hs : IsChain (· ≤ ·) (↑s : Set α)) :
    s.card ≤ longestChain α := by
  refine Finset.le_sup (f := Finset.card) ?_
  simpa using hs

lemma height_le (x : α) : height x ≤ longestChain α := by
  refine Finset.sup_le ?_
  intro s hs
  simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hs
  exact chain_card_le_longestChain hs.1

lemma one_le_height (x : α) : 1 ≤ height x := by
  have : ({x} : Finset α).card ≤ height x := by
    refine Finset.le_sup (f := Finset.card) ?_
    simp only [Set.mem_toFinset, Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · rw [Finset.coe_singleton]
      exact Set.subsingleton_singleton.isChain
    · simp
  simpa using this

lemma height_strictMono {x y : α} (h : x < y) : height x < height y := by
  -- pick a chain in `Iic x` realizing `height x`
  have hne : ({s : Finset α | IsChain (· ≤ ·) (↑s : Set α) ∧ ∀ z ∈ s, z ≤ x}.toFinset).Nonempty := by
    refine ⟨∅, ?_⟩
    simp
  obtain ⟨s, hs, hcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hs
  obtain ⟨hchain, hle⟩ := hs
  have hy : y ∉ s := by
    intro hy
    exact absurd (hle y hy) (not_le_of_gt h)
  have hchain' : IsChain (· ≤ ·) (↑(insert y s) : Set α) := by
    rw [Finset.coe_insert]
    refine hchain.insert ?_
    intro b hb _
    exact Or.inr (le_of_lt (lt_of_le_of_lt (hle b (by simpa using hb)) h))
  have hle' : ∀ z ∈ insert y s, z ≤ y := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact le_refl z
    · exact le_of_lt (lt_of_le_of_lt (hle z hz) h)
  have : (insert y s).card ≤ height y := by
    refine Finset.le_sup (f := Finset.card) ?_
    simp only [Set.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨hchain', hle'⟩
  rw [Finset.card_insert_of_notMem hy] at this
  have hx : height x = s.card := hcard
  omega

/-- The `i`-th level: all elements of height `i`. -/
noncomputable def level (α : Type*) [Fintype α] [PartialOrder α] (i : ℕ) : Finset α :=
  {x : α | height x = i}.toFinset

lemma level_isAntichain (i : ℕ) : IsAntichain (· ≤ ·) (↑(level α i) : Set α) := by
  intro x hx y hy hne hxy
  simp only [level, Set.mem_toFinset, Finset.mem_coe, Set.mem_setOf_eq] at hx hy
  have : height x < height y := height_strictMono (lt_of_le_of_ne hxy hne)
  omega

theorem longestChain_mem_antichainCoverSizes :
    longestChain α ∈ antichainCoverSizes α := by
  refine ⟨(Finset.Icc 1 (longestChain α)).image (fun i => level α i), ?_, ?_, ?_⟩
  · calc ((Finset.Icc 1 (longestChain α)).image (fun i => level α i)).card
        ≤ (Finset.Icc 1 (longestChain α)).card := Finset.card_image_le
      _ = longestChain α := by simp
  · intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact level_isAntichain i
  · intro x
    refine ⟨level α (height x), Finset.mem_image.mpr ⟨height x, ?_, rfl⟩, ?_⟩
    · simp [Finset.mem_Icc, one_le_height x, height_le x]
    · simp [level]

theorem longestChain_le_of_mem_antichainCoverSizes {n : ℕ}
    (hn : n ∈ antichainCoverSizes α) : longestChain α ≤ n := by
  obtain ⟨C, hcard, hanti, hcover⟩ := hn
  refine Finset.sup_le ?_
  intro s hs
  simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hs
  choose g hgC hgmem using hcover
  have hinj : Set.InjOn g ↑s := by
    intro x hx y hy hxy
    by_contra hne
    rcases hs hx hy hne with h | h
    · exact hanti _ (hgC x) (hgmem x) (by rw [hxy]; exact hgmem y) hne h
    · exact hanti _ (hgC y) (hgmem y) (by rw [← hxy]; exact hgmem x) (Ne.symm hne) h
  calc s.card = (s.image g).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ C.card := Finset.card_le_card (by
        intro t ht
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ht
        exact hgC x)
    _ ≤ n := hcard

/-- **Mirsky's theorem** (the dual of Dilworth's theorem): in a finite poset, the minimum
number of antichains needed to cover the poset equals the size of a longest chain. -/
theorem dilworth (α : Type*) [Fintype α] [PartialOrder α] :
    IsLeast (antichainCoverSizes α) (longestChain α) :=
  ⟨longestChain_mem_antichainCoverSizes, fun _ hn => longestChain_le_of_mem_antichainCoverSizes hn⟩

end Math

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

