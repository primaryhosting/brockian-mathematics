/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not allow a module
-- docstring to precede the `import` commands; the module docstring is repeated below.)

import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Math

open Classical in
/-- The largest cardinality of a chain contained in the finset `t`. -/
noncomputable def chainSup {α : Type*} [PartialOrder α] (t : Finset α) : ℕ :=
  t.powerset.sup fun s : Finset α => if IsChain (· ≤ ·) (↑s : Set α) then s.card else 0

/-- The length of a longest chain in the finite poset `α`. -/
noncomputable def maxChainCard (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  chainSup (Finset.univ : Finset α)

/-- The height of `x` : the length of a longest chain all of whose elements are `≤ x`. -/
noncomputable def height {α : Type*} [Fintype α] [PartialOrder α] (x : α) : ℕ :=
  chainSup ((Finset.univ : Finset α).filter fun y => y ≤ x)

variable {α : Type*} [PartialOrder α]

lemma card_le_chainSup {t s : Finset α}
    (hs : s ⊆ t) (hc : IsChain (· ≤ ·) (↑s : Set α)) : s.card ≤ chainSup t := by
  classical
  have h : s ∈ t.powerset := Finset.mem_powerset.mpr hs
  have := Finset.le_sup
    (f := fun s : Finset α => if IsChain (· ≤ ·) (↑s : Set α) then s.card else 0) h
  simpa [chainSup, hc] using this

lemma exists_chain_card_eq_chainSup (t : Finset α) :
    ∃ s : Finset α, s ⊆ t ∧ IsChain (· ≤ ·) (↑s : Set α) ∧ s.card = chainSup t := by
  classical
  have hne : t.powerset.Nonempty := ⟨∅, Finset.empty_mem_powerset t⟩
  obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup t.powerset hne
    (fun s : Finset α => if IsChain (· ≤ ·) (↑s : Set α) then s.card else 0)
  by_cases hc : IsChain (· ≤ ·) (↑s : Set α)
  · exact ⟨s, Finset.mem_powerset.mp hs, hc, by simp [chainSup, hsup, hc]⟩
  · refine ⟨∅, Finset.empty_subset t, by simp [Set.Subsingleton.isChain], ?_⟩
    simp [chainSup, hsup, hc]

lemma chainSup_mono {t u : Finset α} (h : t ⊆ u) : chainSup t ≤ chainSup u := by
  obtain ⟨s, hs, hc, hcard⟩ := exists_chain_card_eq_chainSup t
  exact hcard ▸ card_le_chainSup (hs.trans h) hc

variable [Fintype α]

lemma one_le_height (x : α) : 1 ≤ height x := by
  classical
  have hsub : ({x} : Finset α) ⊆ (Finset.univ : Finset α).filter fun y => y ≤ x := by
    intro y hy
    simp only [Finset.mem_singleton] at hy
    simp [hy]
  have hchain : IsChain (· ≤ ·) ((({x} : Finset α) : Set α)) := by
    simpa using (Set.subsingleton_singleton (a := x)).isChain (r := (· ≤ ·))
  simpa [height] using card_le_chainSup hsub hchain

lemma height_le_maxChainCard (x : α) : height x ≤ maxChainCard α :=
  chainSup_mono (Finset.filter_subset _ _)

lemma height_lt_height {x y : α} (hxy : x < y) : height x < height y := by
  classical
  obtain ⟨s, hs, hc, hcard⟩ :=
    exists_chain_card_eq_chainSup ((Finset.univ : Finset α).filter fun z => z ≤ x)
  have hsx : ∀ z ∈ s, z ≤ x := by
    intro z hz
    have := hs hz
    simp only [Finset.mem_filter] at this
    exact this.2
  have hy : y ∉ s := fun hmem => absurd (lt_of_lt_of_le hxy (hsx y hmem)) (lt_irrefl x)
  have hsy : ∀ z ∈ s, z ≤ y := fun z hz => le_trans (hsx z hz) hxy.le
  have hsub : insert y s ⊆ (Finset.univ : Finset α).filter fun z => z ≤ y := by
    intro z hz
    rcases Finset.mem_insert.mp hz with h | h
    · simp [h]
    · simp only [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hsy z h⟩
  have hchain : IsChain (· ≤ ·) ((insert y s : Finset α) : Set α) := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact Or.inr (hsy b hb)
    · rcases hb with rfl | hb
      · exact Or.inl (hsy a ha)
      · exact hc ha hb hab
  have hle := card_le_chainSup hsub hchain
  rw [Finset.card_insert_of_notMem hy, hcard] at hle
  have h1 : chainSup ((Finset.univ : Finset α).filter fun z => z ≤ x) = height x := rfl
  have h2 : chainSup ((Finset.univ : Finset α).filter fun z => z ≤ y) = height y := rfl
  omega

/-- **Mirsky's theorem** (the dual form of Dilworth's theorem).  In a finite poset, the minimum
number of antichains needed to cover the poset equals the length of a longest chain.

A cover by `n` antichains is encoded as a colouring `f : α → Fin n` whose fibres are antichains,
i.e. such that `x < y` implies `f x ≠ f y`. -/
theorem dilworth (α : Type*) [Fintype α] [PartialOrder α] :
    IsLeast {n : ℕ | ∃ f : α → Fin n, ∀ x y : α, x < y → f x ≠ f y} (maxChainCard α) := by
  classical
  constructor
  · -- the height function provides a colouring with `maxChainCard α` colours
    refine ⟨fun x => ⟨height x - 1, ?_⟩, ?_⟩
    · have h1 := one_le_height x
      have h2 := height_le_maxChainCard x
      omega
    · intro x y hxy hfe
      have h := height_lt_height hxy
      have h1 := one_le_height x
      have h2 := one_le_height y
      have hval : height x - 1 = height y - 1 := congrArg Fin.val hfe
      omega
  · rintro n ⟨f, hf⟩
    obtain ⟨s, -, hc, hcard⟩ := exists_chain_card_eq_chainSup (Finset.univ : Finset α)
    have hinj : Set.InjOn f (↑s : Set α) := by
      intro a ha b hb hab
      by_contra hne
      rcases hc ha hb hne with h | h
      · exact hf a b (lt_of_le_of_ne h hne) hab
      · exact hf b a (lt_of_le_of_ne h (Ne.symm hne)) hab.symm
    have hle : s.card ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card_of_injOn f (fun a _ => Finset.mem_coe.mpr (Finset.mem_univ (f a))) hinj
    simpa [maxChainCard, hcard] using hle

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

