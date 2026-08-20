import Mathlib

/-!
# Dilworth's theorem

In a finite partial order, the minimum number of chains needed to cover the order equals the
maximum size of an antichain.

The main work is done with the auxiliary notion of a *chain colouring*: a map `f : α → ℕ`
assigning to each element of a finite set `s` a colour `< n` such that any two elements of `s`
with the same colour are comparable (i.e. the colour classes are chains).

The main results are:

* `Brockian.Dilworth.dilworth_cover`: if every antichain has at most `n` elements, then the whole
  (finite) order can be covered by at most `n` chains;
* `Brockian.Dilworth.dilworth`: if moreover `n` is attained by some antichain, the cover can be
  taken to consist of exactly `n` chains;
* `Brockian.Dilworth.card_le_card_of_cover`: the converse inequality, i.e. any antichain is at most
  as large as any covering family of chains.

Together, `dilworth` and `card_le_card_of_cover` say that the maximum size of an antichain equals
the minimum number of chains needed to cover the order.

The statement of `dilworth` differs slightly from the one originally posed, which asked for a
cover by exactly `n` chains assuming only that `n` bounds the size of every antichain; that form
is false, and `Brockian.Dilworth.exact_cover_counterexample` gives an explicit counterexample.
-/

namespace Brockian.Dilworth

variable {α : Type*} [PartialOrder α] [DecidableEq α]

/-- `ChainColoring s n f` says that `f` assigns to each element of `s` a colour `< n`, in such a
way that any two elements of `s` with the same colour are comparable; i.e. the colour classes
are chains. -/

lemma step (s : Finset α) (n : ℕ)
    (IH : ∀ t : Finset α, t.card < s.card → ∀ m : ℕ,
      (∀ u ⊆ t, IsAntichain (· ≤ ·) (u : Set α) → u.card ≤ m) → ∃ f : α → ℕ, ChainColoring t m f)
    (h : ∀ t ⊆ s, IsAntichain (· ≤ ·) (t : Set α) → t.card ≤ n) :
    ∃ f : α → ℕ, ChainColoring s n f := by
  classical
  rcases Finset.eq_empty_or_nonempty s with rfl | hs
  · exact ⟨fun _ => 0, by simp, by simp⟩
  obtain ⟨a, ha, b, hb, hba, hamax, hbmin⟩ := exists_max_min hs
  have hn : 1 ≤ n := by
    have h1 : ({a} : Finset α).card ≤ n := by
      refine h {a} (by simpa using ha) ?_
      simp [Set.Subsingleton.isAntichain (Set.subsingleton_singleton) (· ≤ ·)]
    simpa using h1
  have hcardlt : (s \ {a, b}).card < s.card := by
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_of_subset Finset.sdiff_subset]
    exact ⟨a, ha, by simp⟩
  by_cases hcase : ∃ A ⊆ s \ {a, b}, IsAntichain (· ≤ ·) (A : Set α) ∧ A.card = n
  · obtain ⟨A, hAsub, hAanti, hAcard⟩ := hcase
    have hAs : A ⊆ s := hAsub.trans Finset.sdiff_subset
    have haA : a ∉ A := fun hmem => by have := hAsub hmem; simp at this
    have hbA : b ∉ A := fun hmem => by have := hAsub hmem; simp at this
    exact step_case_two ha hb hamax hbmin haA hbA hAs hAanti hAcard h IH
  · push_neg at hcase
    have hbound : ∀ u ⊆ s \ {a, b}, IsAntichain (· ≤ ·) (u : Set α) → u.card ≤ n - 1 := by
      intro u hu hanti
      have h1 : u.card ≤ n := h u (hu.trans Finset.sdiff_subset) hanti
      have h2 : u.card ≠ n := hcase u hu hanti
      omega
    obtain ⟨f', hf'⟩ := IH (s \ {a, b}) hcardlt (n - 1) hbound
    exact step_case_one hba hn hf'

/-- Auxiliary form of Dilworth's theorem, proved by induction on the bound `m` for the size of
`s`, the inductive step being `step`. -/
