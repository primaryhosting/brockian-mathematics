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

set_option grind.warning false

namespace Math

variable {α : Type*} [PartialOrder α]

/-- The finset of all chains (as finsets) contained in a given finset `t`. -/
noncomputable def chainsIn (t : Finset α) : Finset (Finset α) := by
  classical
  exact t.powerset.filter (fun s => IsChain (· ≤ ·) (s : Set α))

lemma mem_chainsIn {t s : Finset α} :
    s ∈ chainsIn t ↔ s ⊆ t ∧ IsChain (· ≤ ·) (s : Set α) := by
  classical
  simp [chainsIn, Finset.mem_filter, Finset.mem_powerset]

/-- The maximal cardinality of a chain contained in `t`. -/
noncomputable def maxChainCardIn (t : Finset α) : ℕ := (chainsIn t).sup Finset.card

lemma card_le_maxChainCardIn {t s : Finset α} (hst : s ⊆ t)
    (hs : IsChain (· ≤ ·) (s : Set α)) : s.card ≤ maxChainCardIn t :=
  Finset.le_sup (f := Finset.card) (mem_chainsIn.2 ⟨hst, hs⟩)

lemma exists_chain_card_eq (t : Finset α) :
    ∃ s : Finset α, s ⊆ t ∧ IsChain (· ≤ ·) (s : Set α) ∧ s.card = maxChainCardIn t := by
  have hne : (chainsIn t).Nonempty := ⟨∅, mem_chainsIn.2 ⟨Finset.empty_subset _, by simp⟩⟩
  obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup (chainsIn t) hne Finset.card
  obtain ⟨h1, h2⟩ := mem_chainsIn.1 hs
  exact ⟨s, h1, h2, (hsup).symm⟩

variable [Fintype α]

/-- The length of a longest chain in the (finite) poset `α`. -/
noncomputable def longestChain (α : Type*) [PartialOrder α] [Fintype α] : ℕ :=
  maxChainCardIn (Finset.univ : Finset α)

/-- The height of an element: the maximal cardinality of a chain below `x`. -/
noncomputable def height (x : α) : ℕ := by
  classical
  exact maxChainCardIn (Finset.univ.filter (fun y => y ≤ x))

/-- `F` is a cover of the poset by antichains. -/
def IsAntichainCover (F : Finset (Finset α)) : Prop :=
  (∀ s ∈ F, IsAntichain (· ≤ ·) (s : Set α)) ∧ ∀ x : α, ∃ s ∈ F, x ∈ s

/-- The minimal number of antichains needed to cover the poset `α`. -/
noncomputable def minAntichainCover (α : Type*) [PartialOrder α] [Fintype α] : ℕ :=
  sInf {n : ℕ | ∃ F : Finset (Finset α), IsAntichainCover F ∧ F.card = n}

/-- Every element has positive height. -/
lemma one_le_height (x : α) : 1 ≤ height x := by
  classical
  have hsub : ({x} : Finset α) ⊆ Finset.univ.filter (fun y => y ≤ x) := by
    intro y hy
    simp only [Finset.mem_singleton] at hy
    subst hy
    simp
  have := card_le_maxChainCardIn hsub (by simp [Set.Subsingleton.isChain])
  simpa [height] using this

/-- The height is bounded by the length of a longest chain. -/
lemma height_le_longestChain (x : α) : height x ≤ longestChain α := by
  classical
  obtain ⟨s, hsub, hchain, hcard⟩ :=
    exists_chain_card_eq (Finset.univ.filter (fun y => y ≤ x))
  have : s.card ≤ longestChain α :=
    card_le_maxChainCardIn (Finset.subset_univ s) hchain
  simpa [height, hcard] using this

/-- The height is strictly monotone. -/
lemma height_lt_height {x y : α} (hxy : x < y) : height x < height y := by
  classical
  obtain ⟨s, hsub, hchain, hcard⟩ :=
    exists_chain_card_eq (Finset.univ.filter (fun z => z ≤ x))
  have hy : y ∉ s := by
    intro hy
    have := hsub hy
    simp only [Finset.mem_filter] at this
    exact absurd (le_antisymm this.2 hxy.le) (by rintro rfl; exact absurd hxy (lt_irrefl _))
  have hsx : ∀ z ∈ s, z ≤ x := by
    intro z hz
    have := hsub hz
    simp only [Finset.mem_filter] at this
    exact this.2
  have hsub' : insert y s ⊆ Finset.univ.filter (fun z => z ≤ y) := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · simp
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact le_trans (hsx z hz) hxy.le
  have hchain' : IsChain (· ≤ ·) ((insert y s : Finset α) : Set α) := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact Or.inr (le_trans (hsx b hb) hxy.le)
    · rcases hb with rfl | hb
      · exact Or.inl (le_trans (hsx a ha) hxy.le)
      · exact hchain ha hb hab
  have hle := card_le_maxChainCardIn hsub' hchain'
  rw [Finset.card_insert_of_notMem hy] at hle
  have : height x + 1 ≤ height y := by
    simpa [height, hcard] using hle
  omega

/-- The fibers of the height function form an antichain cover of size at most
the length of a longest chain. -/
lemma exists_antichain_cover :
    ∃ F : Finset (Finset α), IsAntichainCover F ∧ F.card ≤ longestChain α := by
  classical
  refine ⟨(Finset.Icc 1 (longestChain α)).image
      (fun n => Finset.univ.filter (fun x : α => height x = n)), ⟨?_, ?_⟩, ?_⟩
  · intro s hs
    simp only [Finset.mem_image, Finset.mem_Icc] at hs
    obtain ⟨n, _, rfl⟩ := hs
    intro a ha b hb hab hle
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha hb
    have : height a < height b := height_lt_height (lt_of_le_of_ne hle hab)
    omega
  · intro x
    refine ⟨Finset.univ.filter (fun z : α => height z = height x), ?_, by simp⟩
    simp only [Finset.mem_image, Finset.mem_Icc]
    exact ⟨height x, ⟨one_le_height x, height_le_longestChain x⟩, rfl⟩
  · calc ((Finset.Icc 1 (longestChain α)).image
        (fun n => Finset.univ.filter (fun x : α => height x = n))).card
        ≤ (Finset.Icc 1 (longestChain α)).card := Finset.card_image_le
      _ = longestChain α := by simp

/-- A chain meets every antichain in at most one element, hence any antichain cover
has at least as many parts as the length of a longest chain. -/
lemma longestChain_le_card_of_cover {F : Finset (Finset α)} (hF : IsAntichainCover F) :
    longestChain α ≤ F.card := by
  classical
  obtain ⟨s, -, hchain, hcard⟩ := exists_chain_card_eq (Finset.univ : Finset α)
  choose g hgF hxg using hF.2
  rw [longestChain, ← hcard]
  refine Finset.card_le_card_of_injOn g (fun x _ => hgF x) ?_
  intro x hx y hy hxy
  by_contra hne
  have := hchain (by simpa using hx) (by simpa using hy) hne
  have hanti := hF.1 (g x) (hgF x)
  rcases this with h | h
  · exact hanti (hxg x) (by rw [hxy]; exact hxg y) hne h
  · exact hanti (by rw [hxy]; exact hxg y) (hxg x) (Ne.symm hne) h

/-- **Dilworth-type theorem (Mirsky's theorem).**  In a finite poset, the minimum number of
antichains needed to cover the poset equals the cardinality of a longest chain. -/
theorem dilworth (α : Type*) [PartialOrder α] [Fintype α] :
    minAntichainCover α = longestChain α := by
  classical
  obtain ⟨F, hF, hFcard⟩ := exists_antichain_cover (α := α)
  have hmem : F.card ∈ {n : ℕ | ∃ F : Finset (Finset α), IsAntichainCover F ∧ F.card = n} :=
    ⟨F, hF, rfl⟩
  have hle : minAntichainCover α ≤ longestChain α :=
    le_trans (Nat.sInf_le hmem) hFcard
  have hne : {n : ℕ | ∃ F : Finset (Finset α), IsAntichainCover F ∧ F.card = n}.Nonempty :=
    ⟨F.card, hmem⟩
  obtain ⟨G, hG, hGcard⟩ := Nat.sInf_mem hne
  have hge : longestChain α ≤ minAntichainCover α := by
    rw [minAntichainCover, ← hGcard]
    exact longestChain_le_card_of_cover hG
  omega

end Math

