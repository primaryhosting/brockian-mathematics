/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Statement: In a finite poset, the minimum antichain cover equals the longest chain length.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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
noncomputable def allChains (α : Type*) [Fintype α] [PartialOrder α] : Finset (Finset α) :=
  (Finset.univ : Finset α).powerset.filter (fun C => IsChain (· ≤ ·) (C : Set α))

/-- The length (number of elements) of a longest chain in a finite partial order. -/
noncomputable def longestChain (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  (allChains α).sup Finset.card

/-- The set of sizes of coverings of a finite partial order by antichains. -/
noncomputable def antichainCoverCards (α : Type*) [Fintype α] [PartialOrder α] : Set ℕ :=
  {n | ∃ C : Finset (Finset α), C.card = n ∧
        (∀ A ∈ C, IsAntichain (· ≤ ·) (A : Set α)) ∧ ∀ x : α, ∃ A ∈ C, x ∈ A}

/-- The minimum number of antichains needed to cover a finite partial order. -/
noncomputable def minAntichainCover (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  sInf (antichainCoverCards α)

lemma mem_allChains {C : Finset α} : C ∈ allChains α ↔ IsChain (· ≤ ·) (C : Set α) := by
  simp [allChains]

/-- The finset of chains all of whose elements lie below `x`. -/
noncomputable def chainsBelow (x : α) : Finset (Finset α) :=
  (Finset.univ : Finset α).powerset.filter
    (fun C => IsChain (· ≤ ·) (C : Set α) ∧ ∀ y ∈ C, y ≤ x)

lemma mem_chainsBelow {x : α} {C : Finset α} :
    C ∈ chainsBelow x ↔ IsChain (· ≤ ·) (C : Set α) ∧ ∀ y ∈ C, y ≤ x := by
  simp [chainsBelow]

/-- The rank of `x`: the size of a longest chain ending at `x`. -/
noncomputable def rk (x : α) : ℕ := (chainsBelow x).sup Finset.card

lemma rk_pos (x : α) : 0 < rk x := by
  have h : ({x} : Finset α) ∈ chainsBelow x := by
    rw [mem_chainsBelow]
    refine ⟨?_, ?_⟩
    · simp [IsChain.singleton (r := (· ≤ · : α → α → Prop)) (a := x)]
    · simp
  have := Finset.le_sup (f := Finset.card) h
  simpa [rk] using this

lemma rk_lt_rk {x y : α} (h : x < y) : rk x < rk y := by
  obtain ⟨C, hC, hCsup⟩ :=
    Finset.exists_mem_eq_sup (chainsBelow x) ⟨∅, by rw [mem_chainsBelow]; simp⟩ Finset.card
  rw [mem_chainsBelow] at hC
  obtain ⟨hchain, hbelow⟩ := hC
  have hy : y ∉ C := by
    intro hyC
    exact absurd (hbelow y hyC) h.not_ge
  have hins : insert y C ∈ chainsBelow y := by
    rw [mem_chainsBelow]
    constructor
    · have : IsChain (· ≤ ·) (insert y (C : Set α)) := by
        refine hchain.insert ?_
        intro b hb _
        exact Or.inr (le_trans (hbelow b (by simpa using hb)) h.le)
      simpa using this
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact le_refl _
      · exact le_trans (hbelow z hz) h.le
  have hcard : (insert y C).card = C.card + 1 := Finset.card_insert_of_notMem hy
  have := Finset.le_sup (f := Finset.card) hins
  rw [hcard] at this
  simp only [rk]
  omega

lemma rk_le_longestChain (x : α) : rk x ≤ longestChain α := by
  refine Finset.sup_le ?_
  intro C hC
  rw [mem_chainsBelow] at hC
  exact Finset.le_sup (f := Finset.card) (mem_allChains.2 hC.1)

/-- Level sets of the rank function are antichains. -/
lemma isAntichain_rk_level (i : ℕ) :
    IsAntichain (· ≤ ·) ((Finset.univ.filter (fun z : α => rk z = i) : Finset α) : Set α) := by
  intro a ha b hb hab hle
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha hb
  have : a < b := lt_of_le_of_ne hle hab
  have := rk_lt_rk this
  omega

/-- The cover of the order by the level sets of the rank function. -/
noncomputable def levelCover (α : Type*) [Fintype α] [PartialOrder α] : Finset (Finset α) :=
  (Finset.Icc 1 (longestChain α)).image (fun i => Finset.univ.filter (fun z : α => rk z = i))

/-- The rank levels do form a cover of the order by antichains. -/
lemma levelCover_card_mem : (levelCover α).card ∈ antichainCoverCards α := by
  refine ⟨levelCover α, rfl, ?_, ?_⟩
  · intro A hA
    rw [levelCover, Finset.mem_image] at hA
    obtain ⟨i, _, rfl⟩ := hA
    exact isAntichain_rk_level i
  · intro x
    refine ⟨Finset.univ.filter (fun z : α => rk z = rk x), ?_, ?_⟩
    · rw [levelCover, Finset.mem_image]
      exact ⟨rk x, Finset.mem_Icc.2 ⟨rk_pos x, rk_le_longestChain x⟩, rfl⟩
    · simp

lemma antichainCoverCards_nonempty : (antichainCoverCards α).Nonempty :=
  ⟨_, levelCover_card_mem⟩

lemma minAntichainCover_le_longestChain :
    minAntichainCover α ≤ longestChain α := by
  have h1 : minAntichainCover α ≤ (levelCover α).card := Nat.sInf_le levelCover_card_mem
  have h2 : (levelCover α).card ≤ longestChain α := by
    calc (levelCover α).card ≤ (Finset.Icc 1 (longestChain α)).card := Finset.card_image_le
      _ = longestChain α := by simp
  omega

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
theorem dilworth (α : Type*) [Fintype α] [PartialOrder α] :
    minAntichainCover α = longestChain α :=
  le_antisymm minAntichainCover_le_longestChain
    (le_csInf antichainCoverCards_nonempty (fun _ hn => longestChain_le_of_mem hn))

#print axioms Math.dilworth

end Math

