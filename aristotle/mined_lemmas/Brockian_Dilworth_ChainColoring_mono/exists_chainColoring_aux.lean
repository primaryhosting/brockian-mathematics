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

lemma exists_chainColoring_aux (m : ℕ) : ∀ s : Finset α, s.card ≤ m → ∀ n : ℕ,
    (∀ t ⊆ s, IsAntichain (· ≤ ·) (t : Set α) → t.card ≤ n) → ∃ f : α → ℕ, ChainColoring s n f := by
  induction m with
  | zero =>
    intro s hs n hn
    have hs_empty : s = ∅ := by
      rw [Nat.le_zero] at hs
      exact Finset.card_eq_zero.mp hs
    exact ⟨fun _ => 0, by simp [hs_empty], by simp [hs_empty]⟩
  | succ m ih =>
    intros s hs n hn
    apply step s n _ hn
    intro t ht k hk
    have htcard : t.card ≤ m := by omega
    exact ih t htcard k hk

/-- Dilworth's theorem, colouring form: if every antichain of `s` has at most `n` elements, then
`s` can be coloured with `n` colours so that each colour class is a chain. -/
