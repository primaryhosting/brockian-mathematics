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

set_option grind.warning false

namespace Math

open Finset

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The finset of all chains (as finsets) of a finite partial order. -/
noncomputable def chainFinsets (α : Type*) [Fintype α] [PartialOrder α] : Finset (Finset α) :=
  (Finset.univ : Finset α).powerset.filter (fun c => IsChain (· ≤ ·) (c : Set α))

/-- The maximal cardinality of a chain in a finite partial order. -/
noncomputable def maxChainCard (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  (chainFinsets α).sup Finset.card

/-- The set of sizes `n` such that the poset can be covered by `n` antichains. -/
def antichainCoverNumbers (α : Type*) [PartialOrder α] : Set ℕ :=
  {n | ∃ A : Fin n → Set α, (∀ i, IsAntichain (· ≤ ·) (A i)) ∧ ∀ x : α, ∃ i, x ∈ A i}

/-- The minimal number of antichains needed to cover a finite partial order. -/
noncomputable def minAntichainCover (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  sInf (antichainCoverNumbers α)

lemma mem_chainFinsets {c : Finset α} :
    c ∈ chainFinsets α ↔ IsChain (· ≤ ·) (c : Set α) := by
  simp [chainFinsets]

lemma card_le_maxChainCard {c : Finset α} (hc : IsChain (· ≤ ·) (c : Set α)) :
    c.card ≤ maxChainCard α :=
  Finset.le_sup (f := Finset.card) (mem_chainFinsets.2 hc)

/-- The height of `x`: the maximal cardinality of a chain all of whose elements are `≤ x`. -/
noncomputable def hgt (x : α) : ℕ :=
  ((chainFinsets α).filter (fun c => ∀ y ∈ c, y ≤ x)).sup Finset.card

lemma singleton_mem_hgtFinsets (x : α) :
    ({x} : Finset α) ∈ (chainFinsets α).filter (fun c => ∀ y ∈ c, y ≤ x) := by
  refine Finset.mem_filter.2 ⟨mem_chainFinsets.2 ?_, ?_⟩
  · simp
  · intro y hy
    simp only [Finset.mem_singleton] at hy
    exact hy.le

lemma one_le_hgt (x : α) : 1 ≤ hgt x := by
  have h := Finset.le_sup (f := Finset.card) (singleton_mem_hgtFinsets x)
  rwa [Finset.card_singleton] at h

lemma hgt_le_maxChainCard (x : α) : hgt x ≤ maxChainCard α := by
  refine Finset.sup_le ?_
  intro c hc
  exact card_le_maxChainCard (mem_chainFinsets.1 (Finset.mem_filter.1 hc).1)

lemma hgt_strictMono {x y : α} (hxy : x < y) : hgt x < hgt y := by
  obtain ⟨c, hc, hcard⟩ :=
    Finset.exists_mem_eq_sup ((chainFinsets α).filter (fun c => ∀ y ∈ c, y ≤ x))
      ⟨{x}, singleton_mem_hgtFinsets x⟩ Finset.card
  obtain ⟨hc1, hc2⟩ := Finset.mem_filter.1 hc
  have hchain : IsChain (· ≤ ·) (c : Set α) := mem_chainFinsets.1 hc1
  have hynotmem : y ∉ c := fun hy => absurd (hc2 y hy) (not_le_of_gt hxy)
  have hins : insert y c ∈ (chainFinsets α).filter (fun c => ∀ z ∈ c, z ≤ y) := by
    refine Finset.mem_filter.2 ⟨mem_chainFinsets.2 ?_, ?_⟩
    · have : ((insert y c : Finset α) : Set α) = insert y (c : Set α) := by
        simp
      rw [this]
      refine hchain.insert ?_
      intro b hb _
      exact Or.inr ((hc2 b (by simpa using hb)).trans hxy.le)
    · intro z hz
      rcases Finset.mem_insert.1 hz with h | h
      · exact h ▸ le_refl y
      · exact (hc2 z h).trans hxy.le
  have hle : (insert y c).card ≤ hgt y := Finset.le_sup (f := Finset.card) hins
  rw [Finset.card_insert_of_notMem hynotmem] at hle
  have hx : hgt x = c.card := hcard
  omega

lemma maxChainCard_mem_antichainCoverNumbers :
    maxChainCard α ∈ antichainCoverNumbers α := by
  refine ⟨fun i => {x : α | hgt x = (i : ℕ) + 1}, ?_, ?_⟩
  · intro i a ha b hb hab hle
    have ha' : hgt a = (i : ℕ) + 1 := ha
    have hb' : hgt b = (i : ℕ) + 1 := hb
    have : hgt a < hgt b := hgt_strictMono (lt_of_le_of_ne hle hab)
    omega
  · intro x
    have h1 : 1 ≤ hgt x := one_le_hgt x
    have h2 : hgt x ≤ maxChainCard α := hgt_le_maxChainCard x
    refine ⟨⟨hgt x - 1, by omega⟩, ?_⟩
    show hgt x = (hgt x - 1) + 1
    omega

lemma antichainCoverNumbers_nonempty : (antichainCoverNumbers α).Nonempty := by
  refine ⟨Fintype.card α, fun i => {(Fintype.equivFin α).symm i}, ?_, ?_⟩
  · intro i a ha b hb hab
    simp only [Set.mem_singleton_iff] at ha hb
    exact absurd (ha.trans hb.symm) hab
  · intro x
    exact ⟨Fintype.equivFin α x, by simp⟩

lemma maxChainCard_le_of_mem_antichainCoverNumbers {n : ℕ}
    (hn : n ∈ antichainCoverNumbers α) : maxChainCard α ≤ n := by
  obtain ⟨A, hA, hcov⟩ := hn
  refine Finset.sup_le ?_
  intro c hc
  have hchain : IsChain (· ≤ ·) (c : Set α) := mem_chainFinsets.1 hc
  classical
  set f : α → Fin n := fun x => (hcov x).choose with hf
  have hmem : ∀ x, x ∈ A (f x) := fun x => (hcov x).choose_spec
  have hinj : Set.InjOn f (c : Set α) := by
    intro a ha b hb hab
    by_contra hne
    have hA' := hA (f a)
    rcases hchain ha hb hne with h | h
    · exact hA' (hmem a) (hab ▸ hmem b) hne h
    · exact hA' (hab ▸ hmem b) (hmem a) (Ne.symm hne) h
  have h := Finset.card_le_card_of_injOn (t := (Finset.univ : Finset (Fin n))) f
    (fun a _ => Finset.mem_univ (f a)) hinj
  simpa using h

/-- **Mirsky's theorem** (the dual of Dilworth's theorem): in a finite partial order, the
minimum number of antichains needed to cover the poset equals the maximum cardinality of a
chain. -/
theorem dilworth (α : Type*) [Fintype α] [PartialOrder α] :
    minAntichainCover α = maxChainCard α := by
  refine le_antisymm ?_ ?_
  · exact Nat.sInf_le maxChainCard_mem_antichainCoverNumbers
  · exact maxChainCard_le_of_mem_antichainCoverNumbers
      (Nat.sInf_mem antichainCoverNumbers_nonempty)

end Math

