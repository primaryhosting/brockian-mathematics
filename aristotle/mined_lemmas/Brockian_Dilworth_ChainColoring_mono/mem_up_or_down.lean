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

lemma mem_up_or_down {s A : Finset α} {n : ℕ} (hAs : A ⊆ s)
    (hAanti : IsAntichain (· ≤ ·) (A : Set α)) (hAcard : A.card = n)
    (h : ∀ t ⊆ s, IsAntichain (· ≤ ·) (t : Set α) → t.card ≤ n) {x : α} (hx : x ∈ s) :
    (∃ y ∈ A, x ≤ y) ∨ (∃ y ∈ A, y ≤ x) := by
  by_contra hne
  push_neg at hne
  have hx_notin : x ∉ A := by
    intro hx_in_A
    have := hne.1 x hx_in_A
    exact this (le_refl x)
  have hinsert : IsAntichain (· ≤ ·) (↑(insert x A) : Set α) := by
    rw [Finset.coe_insert]
    apply IsAntichain.insert hAanti
    · intro y hy hxy
      exact hne.2 y hy
    · intro y hy hxy
      exact hne.1 y hy
  have hsub : insert x A ⊆ s := by
    intro z hz
    simp at hz
    rcases hz with rfl | hz
    · exact hx
    · exact hAs hz
  have hcard : (insert x A).card = n + 1 := by
    rw [Finset.card_insert_of_notMem hx_notin, hAcard]
  have := h (insert x A) hsub hinsert
  rw [hcard] at this
  omega

/-- First case of the inductive step: a colouring of `s` with the maximal element `a` and the
minimal element `b ≤ a` removed, using `n - 1` colours, extends to a colouring of `s` with `n`
colours by giving the chain `{b, a}` a fresh colour. -/
