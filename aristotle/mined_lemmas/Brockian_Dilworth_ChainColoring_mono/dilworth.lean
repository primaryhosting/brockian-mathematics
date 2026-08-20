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

theorem dilworth (n : ℕ)
    (hanti : ∀ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) → s.card ≤ n)
    (hn : ∃ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) ∧ s.card = n) :
    ∃ C : Finset (Finset α), C.card = n ∧
      (∀ c ∈ C, IsChain (· ≤ ·) (c : Set α)) ∧
      (∀ a : α, ∃ c ∈ C, a ∈ c) := by
  obtain ⟨s, hsanti, hscard⟩ := hn
  obtain ⟨C, hCle, hCchain, hCover⟩ := dilworth_cover n hanti
  have hsle : s.card ≤ C.card := card_le_card_of_cover s hsanti C hCchain hCover
  exact ⟨C, le_antisymm hCle (hscard ▸ hsle), hCchain, hCover⟩


end Cover

/-!
### The original formulation

The theorem was originally posed with the conclusion `C.card = n`, under the sole hypothesis that
every antichain has at most `n` elements.  In that form it is false: `n` must also be *attained*
by some antichain (as in `dilworth`), since a covering family of chains is a `Finset`, and there
may simply be fewer than `n` distinct chains available.  The following is an explicit
counterexample: the one-element order with `n = 3`.
-/

/-- The original formulation of Dilworth's theorem, which asks for a cover by exactly `n` chains
without assuming that the bound `n` on antichains is attained, is false. -/
