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

variable {α : Type*} [PartialOrder α] [Fintype α]

/-- The finset of all chains of a finite partial order. -/
noncomputable def chainsFinset (α : Type*) [PartialOrder α] [Fintype α] : Finset (Finset α) :=
  Finset.univ.filter (fun C : Finset α => IsChain (· ≤ ·) (C : Set α))

/-- The length (number of elements) of a longest chain of a finite partial order. -/
noncomputable def longestChain (α : Type*) [PartialOrder α] [Fintype α] : ℕ :=
  (chainsFinset α).sup Finset.card

/-- The height of `x`: the size of a longest chain all of whose elements are `≤ x`. -/
noncomputable def height (x : α) : ℕ :=
  ((chainsFinset α).filter (fun C => ∀ y ∈ C, y ≤ x)).sup Finset.card

/-- `S` is a cover of the poset by antichains. -/
def IsAntichainCover (S : Finset (Finset α)) : Prop :=
  (∀ A ∈ S, IsAntichain (· ≤ ·) (A : Set α)) ∧ ∀ x : α, ∃ A ∈ S, x ∈ A

/-- The minimum number of antichains needed to cover a finite partial order. -/
noncomputable def antichainCoverNumber (α : Type*) [PartialOrder α] [Fintype α] : ℕ :=
  sInf {n : ℕ | ∃ S : Finset (Finset α), S.card = n ∧ IsAntichainCover S}

lemma mem_chainsFinset {C : Finset α} :
    C ∈ chainsFinset α ↔ IsChain (· ≤ ·) (C : Set α) := by
  simp [chainsFinset]

lemma chainsFinset_nonempty : (chainsFinset α).Nonempty :=
  ⟨(∅ : Finset α), by simp [mem_chainsFinset, Set.Subsingleton.isChain]⟩

lemma exists_longest_chain : ∃ C ∈ chainsFinset α, C.card = longestChain α := by
  obtain ⟨C, hC, hCcard⟩ :=
    Finset.exists_mem_eq_sup (chainsFinset α) chainsFinset_nonempty Finset.card
  exact ⟨C, hC, hCcard.symm⟩

lemma height_le_longestChain (x : α) : height x ≤ longestChain α := by
  refine Finset.sup_mono ?_
  exact Finset.filter_subset _ _

lemma one_le_height (x : α) : 1 ≤ height x := by
  have hx : ({x} : Finset α) ∈ (chainsFinset α).filter (fun C => ∀ y ∈ C, y ≤ x) := by
    simp only [Finset.mem_filter, mem_chainsFinset]
    refine ⟨?_, ?_⟩
    · simp
    · intro y hy
      simp only [Finset.mem_singleton] at hy
      exact hy.le
  have h := Finset.le_sup (f := Finset.card) hx
  simp only [Finset.card_singleton] at h
  exact h

lemma height_strictMono {x y : α} (hxy : x < y) : height x < height y := by
  have hne : ((chainsFinset α).filter (fun C => ∀ z ∈ C, z ≤ x)).Nonempty := by
    refine ⟨{x}, ?_⟩
    simp only [Finset.mem_filter, mem_chainsFinset]
    refine ⟨by simp, ?_⟩
    intro z hz
    simp only [Finset.mem_singleton] at hz
    exact hz.le
  obtain ⟨C, hC, hCcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  simp only [Finset.mem_filter, mem_chainsFinset] at hC
  obtain ⟨hchain, hle⟩ := hC
  have hyC : y ∉ C := by
    intro hy
    exact absurd (lt_of_lt_of_le hxy (hle y hy)) (lt_irrefl x)
  have hins : (insert y C) ∈ (chainsFinset α).filter (fun C => ∀ z ∈ C, z ≤ y) := by
    simp only [Finset.mem_filter, mem_chainsFinset]
    constructor
    · rw [Finset.coe_insert]
      refine hchain.insert ?_
      intro b hb _
      exact Or.inr (le_trans (hle b (by exact_mod_cast hb)) hxy.le)
    · intro z hz
      rcases Finset.mem_insert.1 hz with h | h
      · exact h.le
      · exact le_trans (hle z h) hxy.le
  have h1 : (insert y C).card = C.card + 1 := Finset.card_insert_of_notMem hyC
  have h2 : (insert y C).card ≤ height y := Finset.le_sup (f := Finset.card) hins
  rw [height, hCcard]
  omega

lemma isAntichain_level (k : ℕ) :
    IsAntichain (· ≤ ·) ((Finset.univ.filter (fun x : α => height x = k) : Finset α) : Set α) := by
  intro a ha b hb hab hle
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
  have : height a < height b := height_strictMono (lt_of_le_of_ne hle hab)
  omega

lemma exists_small_cover :
    ∃ S : Finset (Finset α), IsAntichainCover S ∧ S.card ≤ longestChain α := by
  set S : Finset (Finset α) :=
    (Finset.Icc 1 (longestChain α)).image
      (fun k => Finset.univ.filter (fun x : α => height x = k)) with hS
  have hcover : IsAntichainCover S := by
    constructor
    · intro A hA
      simp only [hS, Finset.mem_image] at hA
      obtain ⟨k, _, rfl⟩ := hA
      exact isAntichain_level k
    · intro x
      refine ⟨Finset.univ.filter (fun z : α => height z = height x), ?_, by simp⟩
      simp only [hS, Finset.mem_image]
      exact ⟨height x, Finset.mem_Icc.2 ⟨one_le_height x, height_le_longestChain x⟩, rfl⟩
  have hcard : S.card ≤ longestChain α := by
    calc S.card ≤ (Finset.Icc 1 (longestChain α)).card := Finset.card_image_le
      _ = longestChain α := by simp
  exact ⟨S, hcover, hcard⟩

lemma antichainCoverNumber_le : antichainCoverNumber α ≤ longestChain α := by
  obtain ⟨S, hcover, hcard⟩ := exists_small_cover (α := α)
  have hmem : S.card ∈ {n : ℕ | ∃ T : Finset (Finset α), T.card = n ∧ IsAntichainCover T} :=
    ⟨S, rfl, hcover⟩
  exact le_trans (Nat.sInf_le hmem) hcard

lemma longestChain_le_card_of_cover {S : Finset (Finset α)} (h : IsAntichainCover S) :
    longestChain α ≤ S.card := by
  obtain ⟨C, hC, hCcard⟩ := exists_longest_chain (α := α)
  rw [mem_chainsFinset] at hC
  choose f hfS hfmem using h.2
  have hinj : Set.InjOn f (C : Set α) := by
    intro a ha b hb hfab
    by_contra hab
    have hcomp := hC ha hb hab
    have hA : IsAntichain (· ≤ ·) ((f a : Finset α) : Set α) := h.1 _ (hfS a)
    have hbmem : b ∈ (f a : Finset α) := by rw [hfab]; exact hfmem b
    rcases hcomp with hle | hle
    · exact hA (by exact_mod_cast hfmem a) (by exact_mod_cast hbmem) hab hle
    · exact hA (by exact_mod_cast hbmem) (by exact_mod_cast hfmem a) (Ne.symm hab) hle
  have : C.card ≤ S.card := by
    refine Finset.card_le_card_of_injOn f (fun a ha => hfS a) ?_
    intro a ha b hb hfab
    exact hinj (by exact_mod_cast ha) (by exact_mod_cast hb) hfab
  omega

/-- **Mirsky's theorem**: in a finite poset, the minimum number of antichains needed to
cover the poset equals the number of elements of a longest chain. -/
theorem dilworth (α : Type*) [PartialOrder α] [Fintype α] :
    antichainCoverNumber α = longestChain α := by
  refine le_antisymm antichainCoverNumber_le ?_
  obtain ⟨S₀, hcover₀, -⟩ := exists_small_cover (α := α)
  have hne : {n : ℕ | ∃ S : Finset (Finset α), S.card = n ∧ IsAntichainCover S}.Nonempty :=
    ⟨S₀.card, S₀, rfl, hcover₀⟩
  refine le_csInf hne ?_
  rintro n ⟨S, rfl, hS⟩
  exact longestChain_le_card_of_cover hS

/-- Sanity check: in a finite linear order every subset is a chain, so the longest chain has
`Fintype.card α` elements and one needs that many antichains (singletons) to cover. -/
example (α : Type*) [LinearOrder α] [Fintype α] :
    antichainCoverNumber α = Fintype.card α := by
  rw [dilworth]
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le ?_
    intro C _
    exact Finset.card_le_univ C
  · have huniv : (Finset.univ : Finset α) ∈ chainsFinset α := by
      rw [mem_chainsFinset]
      intro a _ b _ hab
      exact le_total a b
    simpa using Finset.le_sup (f := Finset.card) huniv

end Math

