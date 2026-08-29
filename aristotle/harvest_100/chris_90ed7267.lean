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

/-- The largest cardinality of a chain contained in the finite set `t`. -/
noncomputable def chainSup (t : Finset α) : ℕ :=
  (t.powerset.filter fun s : Finset α => IsChain (· ≤ ·) (↑s : Set α)).sup Finset.card

/-- The length of a longest chain in the finite poset `α`. -/
noncomputable def longestChainCard (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  chainSup (Finset.univ : Finset α)

/-- A finite family of subsets of `α` is an *antichain cover* when each member is an
antichain and every element lies in some member. -/
def IsAntichainCover (F : Finset (Finset α)) : Prop :=
  (∀ s ∈ F, IsAntichain (· ≤ ·) (s : Set α)) ∧ ∀ x : α, ∃ s ∈ F, x ∈ s

/-- The minimum number of antichains needed to cover the finite poset `α`. -/
noncomputable def minAntichainCoverCard (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  sInf {n | ∃ F : Finset (Finset α), F.card ≤ n ∧ IsAntichainCover F}

/-- The `height` of `x` is the length of a longest chain in the down-set of `x`. -/
noncomputable def height (x : α) : ℕ :=
  chainSup (Finset.univ.filter fun y => y ≤ x)

omit [Fintype α] in
lemma card_le_chainSup {s t : Finset α} (hst : s ⊆ t) (hs : IsChain (· ≤ ·) (s : Set α)) :
    s.card ≤ chainSup t :=
  Finset.le_sup (f := Finset.card) (by simp [Finset.mem_filter, Finset.mem_powerset, hst, hs])

omit [Fintype α] in
lemma chainSup_mono {t u : Finset α} (h : t ⊆ u) : chainSup t ≤ chainSup u := by
  refine Finset.sup_le ?_
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_powerset] at hs
  exact card_le_chainSup (hs.1.trans h) hs.2

omit [Fintype α] in
lemma exists_chain_card_eq_chainSup (t : Finset α) :
    ∃ s ⊆ t, IsChain (· ≤ ·) (s : Set α) ∧ s.card = chainSup t := by
  have hne : (t.powerset.filter fun s : Finset α => IsChain (· ≤ ·) (↑s : Set α)).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [Finset.mem_filter, Finset.mem_powerset]
  obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  simp only [Finset.mem_filter, Finset.mem_powerset] at hs
  exact ⟨s, hs.1, hs.2, hsup.symm⟩

lemma one_le_height (x : α) : 1 ≤ height x := by
  have : ({x} : Finset α).card ≤ height x := by
    refine card_le_chainSup ?_ ?_
    · simp
    · simp only [Finset.coe_singleton]
      exact Set.subsingleton_singleton.isChain
  simpa using this

lemma height_le_longestChainCard (x : α) : height x ≤ longestChainCard α :=
  chainSup_mono (Finset.filter_subset _ _)

lemma height_lt_height {x y : α} (hxy : x < y) : height x < height y := by
  obtain ⟨s, hs, hchain, hcard⟩ :=
    exists_chain_card_eq_chainSup (Finset.univ.filter fun z => z ≤ x)
  have hsx : ∀ z ∈ s, z ≤ x := by
    intro z hz
    simpa using hs hz
  have hynot : y ∉ s := by
    intro hy
    exact absurd (lt_of_lt_of_le hxy (hsx y hy)) (lt_irrefl x)
  have hsub : insert y s ⊆ Finset.univ.filter fun z => z ≤ y := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · simp
    · simpa using le_of_lt (lt_of_le_of_lt (hsx z hz) hxy)
  have hchain' : IsChain (· ≤ ·) ((insert y s : Finset α) : Set α) := by
    have : ((insert y s : Finset α) : Set α) = insert y (s : Set α) := by
      simp
    rw [this]
    refine hchain.insert ?_
    intro b hb _
    exact Or.inr (le_of_lt (lt_of_le_of_lt (hsx b hb) hxy))
  have := card_le_chainSup hsub hchain'
  rw [Finset.card_insert_of_notMem hynot, hcard] at this
  exact lt_of_lt_of_le (Nat.lt_succ_self _) this

lemma antichain_level (i : ℕ) :
    IsAntichain (· ≤ ·) ((Finset.univ.filter fun x : α => height x = i : Finset α) : Set α) := by
  intro x hx y hy hne hle
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx hy
  have : x < y := lt_of_le_of_ne hle hne
  have := height_lt_height this
  omega

/-- Every antichain cover has at least as many members as the longest chain. -/
lemma longestChainCard_le_card_of_cover {F : Finset (Finset α)} (hF : IsAntichainCover F) :
    longestChainCard α ≤ F.card := by
  obtain ⟨C, -, hchain, hcard⟩ := exists_chain_card_eq_chainSup (Finset.univ : Finset α)
  have hpick : ∀ x : α, ∃ s, s ∈ F ∧ x ∈ s := fun x => hF.2 x
  choose g hgF hgmem using hpick
  have hinj : Set.InjOn g (C : Set α) := by
    intro x hx y hy hxy
    by_contra hne
    have hax := hF.1 (g x) (hgF x)
    have hxs : x ∈ (g x : Set α) := hgmem x
    have hys : y ∈ (g x : Set α) := by rw [hxy]; exact hgmem y
    rcases hchain hx hy hne with h | h
    · exact hax hxs hys hne h
    · exact hax hys hxs (Ne.symm hne) h
  have := Finset.card_le_card_of_injOn g (fun x _ => hgF x) hinj
  rw [longestChainCard, ← hcard]
  exact this

/-- The levels of the height function form an antichain cover with at most
`longestChainCard α` members. -/
lemma exists_cover_card_le_longestChainCard :
    ∃ F : Finset (Finset α), F.card ≤ longestChainCard α ∧ IsAntichainCover F := by
  refine ⟨(Finset.Icc 1 (longestChainCard α)).image
      (fun i => Finset.univ.filter fun x : α => height x = i), ?_, ?_, ?_⟩
  · exact le_trans (Finset.card_image_le) (by simp)
  · intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    exact antichain_level i
  · intro x
    refine ⟨Finset.univ.filter fun y : α => height y = height x, ?_, by simp⟩
    exact Finset.mem_image.mpr
      ⟨height x, Finset.mem_Icc.mpr ⟨one_le_height x, height_le_longestChainCard x⟩, rfl⟩

/-- **Mirsky's theorem** (the dual of Dilworth's theorem): in a finite poset, the minimum
number of antichains needed to cover the poset equals the length of a longest chain. -/
theorem dilworth (α : Type*) [Fintype α] [PartialOrder α] :
    minAntichainCoverCard α = longestChainCard α := by
  have hmem : longestChainCard α ∈ {n | ∃ F : Finset (Finset α), F.card ≤ n ∧ IsAntichainCover F} :=
    exists_cover_card_le_longestChainCard
  refine le_antisymm (Nat.sInf_le hmem) ?_
  refine le_csInf ⟨_, hmem⟩ ?_
  rintro n ⟨F, hcard, hF⟩
  exact le_trans (longestChainCard_le_card_of_cover hF) hcard

/-- Sanity check: the longest chain in the linear order `Fin 3` has three elements, so the
minimum antichain cover of `Fin 3` also has three parts. -/
example : longestChainCard (Fin 3) = 3 := by
  rw [longestChainCard, chainSup]
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_powerset] at hs
    simpa using Finset.card_le_card hs.1
  · have : (Finset.univ : Finset (Fin 3)).card ≤ chainSup (Finset.univ : Finset (Fin 3)) :=
      Finset.le_sup (f := Finset.card) (by simp [IsChain, Set.Pairwise, le_total])
    simpa [chainSup] using this

end Math

#print axioms Math.dilworth

