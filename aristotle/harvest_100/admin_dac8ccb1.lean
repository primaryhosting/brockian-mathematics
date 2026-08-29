/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

open scoped Classical in
/-- The maximal cardinality of a chain in a finite partial order. -/
noncomputable def maxChainLen (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  (Finset.univ.filter (fun c : Finset α => IsChain (· ≤ ·) (c : Set α))).sup Finset.card

open scoped Classical in
/-- The height of `x`: the maximal cardinality of a chain all of whose elements are `≤ x`. -/
noncomputable def height {α : Type*} [Fintype α] [PartialOrder α] (x : α) : ℕ :=
  (Finset.univ.filter
    (fun c : Finset α => IsChain (· ≤ ·) (c : Set α) ∧ ∀ y ∈ c, y ≤ x)).sup Finset.card

variable {α : Type*} [Fintype α] [PartialOrder α]

lemma card_le_maxChainLen {c : Finset α} (hc : IsChain (· ≤ ·) (c : Set α)) :
    c.card ≤ maxChainLen α := by
  classical
  exact Finset.le_sup (f := Finset.card) (by simpa [maxChainLen] using hc)

lemma exists_chain_card_eq_maxChainLen :
    ∃ c : Finset α, IsChain (· ≤ ·) (c : Set α) ∧ c.card = maxChainLen α := by
  classical
  obtain ⟨c, hc, hsup⟩ :=
    Finset.exists_mem_eq_sup
      (Finset.univ.filter (fun c : Finset α => IsChain (· ≤ ·) (c : Set α)))
      ⟨∅, by simp⟩ Finset.card
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  exact ⟨c, hc, (hsup.symm : _)⟩

lemma card_le_height {c : Finset α} {x : α} (hc : IsChain (· ≤ ·) (c : Set α))
    (hx : ∀ y ∈ c, y ≤ x) : c.card ≤ height x := by
  classical
  refine Finset.le_sup (f := Finset.card) ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hc, hx⟩

lemma exists_chain_card_eq_height (x : α) :
    ∃ c : Finset α, IsChain (· ≤ ·) (c : Set α) ∧ (∀ y ∈ c, y ≤ x) ∧ c.card = height x := by
  classical
  obtain ⟨c, hc, hsup⟩ :=
    Finset.exists_mem_eq_sup
      (Finset.univ.filter
        (fun c : Finset α => IsChain (· ≤ ·) (c : Set α) ∧ ∀ y ∈ c, y ≤ x))
      ⟨∅, by simp⟩ Finset.card
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  exact ⟨c, hc.1, hc.2, (hsup.symm : _)⟩

lemma height_pos (x : α) : 0 < height x := by
  have h : ({x} : Finset α).card ≤ height x := by
    refine card_le_height ?_ ?_
    · simp
    · simp
  simpa using h

lemma height_le_maxChainLen (x : α) : height x ≤ maxChainLen α := by
  classical
  refine Finset.sup_le ?_
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  exact card_le_maxChainLen hc.1

lemma height_lt_height {x y : α} (h : x < y) : height x < height y := by
  classical
  obtain ⟨c, hc, hcx, hcard⟩ := exists_chain_card_eq_height x
  have hy : y ∉ c := fun hy => absurd (hcx y hy) (not_le_of_gt h)
  have hchain : IsChain (· ≤ ·) ((insert y c : Finset α) : Set α) := by
    rw [Finset.coe_insert]
    refine hc.insert ?_
    intro b hb _
    exact Or.inr (le_of_lt (lt_of_le_of_lt (hcx b hb) h))
  have hle : ∀ z ∈ insert y c, z ≤ y := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact le_rfl
    · exact le_of_lt (lt_of_le_of_lt (hcx z hz) h)
  have := card_le_height hchain hle
  rw [Finset.card_insert_of_notMem hy, hcard] at this
  omega

/-- **Mirsky's theorem** (the dual form of Dilworth's theorem):
in a finite partial order, the least number of antichains needed to cover the order
equals the maximal cardinality of a chain. -/
theorem dilworth (α : Type*) [Fintype α] [PartialOrder α] :
    IsLeast {n : ℕ | ∃ A : Fin n → Finset α,
        (∀ i, IsAntichain (· ≤ ·) (A i : Set α)) ∧ ∀ x : α, ∃ i, x ∈ A i}
      (maxChainLen α) := by
  classical
  constructor
  · -- the height function provides a cover by `maxChainLen α` antichains
    refine ⟨fun i => Finset.univ.filter (fun x : α => height x - 1 = (i : ℕ)), ?_, ?_⟩
    · intro i x hx y hy hxy hle
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx hy
      have hlt : x < y := lt_of_le_of_ne hle hxy
      have := height_lt_height hlt
      have hx1 := height_pos x
      have hy1 := height_pos y
      omega
    · intro x
      have h1 := height_pos x
      have h2 := height_le_maxChainLen x
      exact ⟨⟨height x - 1, by omega⟩, by simp⟩
  · -- any cover by `n` antichains has `n ≥ maxChainLen α`
    rintro n ⟨A, hA, hcov⟩
    obtain ⟨c, hc, hcard⟩ := exists_chain_card_eq_maxChainLen (α := α)
    set g : α → ℕ := fun x => ((Classical.choose (hcov x) : Fin n) : ℕ) with hg
    have hmem : ∀ x : α, x ∈ A (Classical.choose (hcov x)) := fun x => Classical.choose_spec (hcov x)
    have hcard' : c.card ≤ (Finset.range n).card := by
      refine Finset.card_le_card_of_injOn g ?_ ?_
      · intro x _
        simp only [Finset.coe_range, Set.mem_Iio, hg]
        exact (Classical.choose (hcov x)).isLt
      · intro x hx y hy hxy
        by_contra hne
        have hidx : Classical.choose (hcov x) = Classical.choose (hcov y) :=
          Fin.ext (by simpa [hg] using hxy)
        have hxA : x ∈ A (Classical.choose (hcov y)) := hidx ▸ hmem x
        have hyA : y ∈ A (Classical.choose (hcov y)) := hmem y
        have hanti := hA (Classical.choose (hcov y))
        rcases hc hx hy hne with h | h
        · exact hanti hxA hyA hne h
        · exact hanti hyA hxA (Ne.symm hne) h
    simpa [hcard, Finset.card_range] using hcard'

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

