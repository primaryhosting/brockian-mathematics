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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open Finset

variable {α : Type*} [Fintype α] [PartialOrder α]

open Classical in
/-- `chainHeight x` is the largest cardinality of a chain all of whose elements are `≤ x`. -/
noncomputable def chainHeight (x : α) : ℕ :=
  (Finset.univ : Finset (Finset α)).sup
    (fun s => if IsChain (· ≤ ·) (s : Set α) ∧ ∀ y ∈ s, y ≤ x then s.card else 0)

lemma one_le_chainHeight (x : α) : 1 ≤ chainHeight x := by
  classical
  have h := Finset.le_sup (f := fun s : Finset α =>
      if IsChain (· ≤ ·) (s : Set α) ∧ ∀ y ∈ s, y ≤ x then s.card else 0)
    (Finset.mem_univ ({x} : Finset α))
  have hcond : IsChain (· ≤ ·) (({x} : Finset α) : Set α) ∧ ∀ y ∈ ({x} : Finset α), y ≤ x := by
    refine ⟨?_, ?_⟩
    · simp [Finset.coe_singleton, Set.Subsingleton.isChain]
    · intro y hy
      simp only [Finset.mem_singleton] at hy
      exact hy.le
  rw [chainHeight]
  simpa [hcond] using h

lemma chainHeight_le_of_isGreatest {M : ℕ}
    (hM : IsGreatest {n : ℕ | ∃ s : Finset α, IsChain (· ≤ ·) (s : Set α) ∧ s.card = n} M)
    (x : α) : chainHeight x ≤ M := by
  classical
  rw [chainHeight]
  refine Finset.sup_le ?_
  intro s _
  split
  · rename_i hs
    exact hM.2 ⟨s, hs.1, rfl⟩
  · exact Nat.zero_le _

lemma exists_chain_chainHeight (x : α) :
    ∃ s : Finset α, IsChain (· ≤ ·) (s : Set α) ∧ (∀ y ∈ s, y ≤ x) ∧ s.card = chainHeight x := by
  classical
  obtain ⟨s, -, hs⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Finset α))
    ⟨(∅ : Finset α), Finset.mem_univ _⟩
    (fun s : Finset α =>
      if IsChain (· ≤ ·) (s : Set α) ∧ ∀ y ∈ s, y ≤ x then s.card else 0)
  by_cases hcond : IsChain (· ≤ ·) (s : Set α) ∧ ∀ y ∈ s, y ≤ x
  · refine ⟨s, hcond.1, hcond.2, ?_⟩
    rw [chainHeight, hs, if_pos hcond]
  · exfalso
    have : chainHeight x = 0 := by rw [chainHeight, hs, if_neg hcond]
    have := one_le_chainHeight x
    omega

lemma chainHeight_lt_of_lt {x y : α} (hxy : x < y) : chainHeight x < chainHeight y := by
  classical
  obtain ⟨s, hchain, hle, hcard⟩ := exists_chain_chainHeight x
  have hy : y ∉ s := by
    intro hy
    exact absurd (hle y hy) (not_le_of_gt hxy)
  set t : Finset α := insert y s with ht
  have htchain : IsChain (· ≤ ·) (t : Set α) := by
    rw [ht, Finset.coe_insert]
    refine hchain.insert ?_
    intro b hb _
    have : b ≤ x := hle b (by simpa using hb)
    exact Or.inr (this.trans hxy.le)
  have htle : ∀ z ∈ t, z ≤ y := by
    intro z hz
    rw [ht, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact le_rfl
    · exact (hle z hz).trans hxy.le
  have hcardt : t.card = s.card + 1 := by
    rw [ht, Finset.card_insert_of_notMem hy]
  have hsup := Finset.le_sup (f := fun s : Finset α =>
      if IsChain (· ≤ ·) (s : Set α) ∧ ∀ z ∈ s, z ≤ y then s.card else 0)
    (Finset.mem_univ t)
  simp only [] at hsup
  rw [if_pos (⟨htchain, htle⟩ : IsChain (· ≤ ·) (t : Set α) ∧ ∀ z ∈ t, z ≤ y)] at hsup
  have : t.card ≤ chainHeight y := by
    rw [chainHeight]; exact hsup
  omega

/-- Every level set of `chainHeight` is an antichain. -/
lemma isAntichain_level (k : ℕ) :
    IsAntichain (· ≤ ·)
      ((Finset.univ.filter (fun x : α => chainHeight x - 1 = k) : Finset α) : Set α) := by
  classical
  intro a ha b hb hab hle
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha hb
  have hlt : a < b := lt_of_le_of_ne hle hab
  have := chainHeight_lt_of_lt hlt
  have h1 := one_le_chainHeight a
  have h2 := one_le_chainHeight b
  omega

omit [Fintype α] in
/-- A cover by antichains has at least as many parts as any chain has elements. -/
lemma card_chain_le_card_cover {F : Finset (Finset α)}
    (hanti : ∀ A ∈ F, IsAntichain (· ≤ ·) (A : Set α)) (hcov : ∀ x : α, ∃ A ∈ F, x ∈ A)
    {s : Finset α} (hs : IsChain (· ≤ ·) (s : Set α)) : s.card ≤ F.card := by
  classical
  choose pick hpickF hpickmem using hcov
  refine Finset.card_le_card_of_injOn pick (fun x _ => hpickF x) ?_
  intro x hx y hy hxy
  by_contra hne
  have hxA : x ∈ pick x := hpickmem x
  have hyA : y ∈ pick x := hxy ▸ hpickmem y
  have hanti' := hanti (pick x) (hpickF x)
  rcases hs (by simpa using hx) (by simpa using hy) hne with h | h
  · exact hanti' hxA hyA hne h
  · exact hanti' hyA hxA (Ne.symm hne) h


open Classical in
/-- The maximum size of a chain in a finite partial order. -/
noncomputable def maxChainCard (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  (Finset.univ : Finset (Finset α)).sup
    (fun s => if IsChain (· ≤ ·) (s : Set α) then s.card else 0)

/-- In a finite partial order there really is a longest chain, so the hypothesis of
`Math.dilworth` is always satisfiable. -/
lemma isGreatest_maxChainCard (α : Type*) [Fintype α] [PartialOrder α] :
    IsGreatest {n : ℕ | ∃ s : Finset α, IsChain (· ≤ ·) (s : Set α) ∧ s.card = n}
      (maxChainCard α) := by
  classical
  constructor
  · obtain ⟨s, -, hs⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Finset α))
      ⟨(∅ : Finset α), Finset.mem_univ _⟩
      (fun s : Finset α => if IsChain (· ≤ ·) (s : Set α) then s.card else 0)
    by_cases hc : IsChain (· ≤ ·) (s : Set α)
    · exact ⟨s, hc, by rw [maxChainCard, hs, if_pos hc]⟩
    · refine ⟨(∅ : Finset α), Set.Subsingleton.isChain (by simp), ?_⟩
      rw [maxChainCard, hs, if_neg hc]
      simp
  · rintro n ⟨s, hs, rfl⟩
    have hsup := Finset.le_sup (f := fun s : Finset α =>
        if IsChain (· ≤ ·) (s : Set α) then s.card else 0) (Finset.mem_univ s)
    simp only [] at hsup
    rw [if_pos hs] at hsup
    exact hsup

/-- **Mirsky's theorem** (the dual of Dilworth's theorem): in a finite partial order, the
minimum number of antichains needed to cover the whole order equals the maximum size of a
chain. -/
theorem dilworth (α : Type*) [Fintype α] [PartialOrder α] (M : ℕ)
    (hM : IsGreatest {n : ℕ | ∃ s : Finset α, IsChain (· ≤ ·) (s : Set α) ∧ s.card = n} M) :
    IsLeast {n : ℕ | ∃ F : Finset (Finset α), F.card = n ∧
      (∀ A ∈ F, IsAntichain (· ≤ ·) (A : Set α)) ∧ (∀ x : α, ∃ A ∈ F, x ∈ A)} M := by
  classical
  constructor
  · -- construct a cover by `M` antichains
    set F : Finset (Finset α) :=
      (Finset.range M).image (fun k => Finset.univ.filter (fun x : α => chainHeight x - 1 = k))
      with hF
    have hanti : ∀ A ∈ F, IsAntichain (· ≤ ·) (A : Set α) := by
      intro A hA
      rw [hF, Finset.mem_image] at hA
      obtain ⟨k, -, rfl⟩ := hA
      exact isAntichain_level k
    have hcov : ∀ x : α, ∃ A ∈ F, x ∈ A := by
      intro x
      refine ⟨Finset.univ.filter (fun y : α => chainHeight y - 1 = chainHeight x - 1), ?_, ?_⟩
      · rw [hF, Finset.mem_image]
        refine ⟨chainHeight x - 1, ?_, rfl⟩
        have h1 := one_le_chainHeight x
        have h2 := chainHeight_le_of_isGreatest hM x
        simp only [Finset.mem_range]
        omega
      · simp
    have hle : F.card ≤ M := by
      refine le_trans (Finset.card_image_le) ?_
      simp
    have hge : M ≤ F.card := by
      obtain ⟨s, hchain, hcard⟩ := hM.1
      calc M = s.card := hcard.symm
        _ ≤ F.card := card_chain_le_card_cover hanti hcov hchain
    exact ⟨F, le_antisymm hle hge, hanti, hcov⟩
  · rintro n ⟨F, rfl, hanti, hcov⟩
    obtain ⟨s, hchain, hcard⟩ := hM.1
    calc M = s.card := hcard.symm
      _ ≤ F.card := card_chain_le_card_cover hanti hcov hchain

/-- Unconditional form: the minimum number of antichains covering a finite partial order
equals the maximum size of a chain. -/
theorem dilworth' (α : Type*) [Fintype α] [PartialOrder α] :
    IsGreatest {n : ℕ | ∃ s : Finset α, IsChain (· ≤ ·) (s : Set α) ∧ s.card = n}
        (maxChainCard α) ∧
      IsLeast {n : ℕ | ∃ F : Finset (Finset α), F.card = n ∧
        (∀ A ∈ F, IsAntichain (· ≤ ·) (A : Set α)) ∧ (∀ x : α, ∃ A ∈ F, x ∈ A)}
        (maxChainCard α) :=
  ⟨isGreatest_maxChainCard α, dilworth α _ (isGreatest_maxChainCard α)⟩

end Math

