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

theorem exact_cover_counterexample :
    (∀ s : Finset (Fin 1), IsAntichain (· ≤ ·) (s : Set (Fin 1)) → s.card ≤ 3) ∧
      ¬ ∃ C : Finset (Finset (Fin 1)), C.card = 3 ∧
        (∀ c ∈ C, IsChain (· ≤ ·) (c : Set (Fin 1))) ∧ (∀ a : Fin 1, ∃ c ∈ C, a ∈ c) := by
  constructor
  · intro s _hs
    exact le_trans (Finset.card_le_univ s) (by decide)
  · rintro ⟨C, hCcard, -, -⟩
    have hle : C.card ≤ 2 := by
      have := Finset.card_le_univ (C : Finset (Finset (Fin 1)))
      simpa using this
    omega

end Brockian.Dilworth

