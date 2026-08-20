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

lemma ChainColoring.exists_of_lt {s A : Finset α} {n : ℕ} {f : α → ℕ}
    (h : ChainColoring s n f) (hAs : A ⊆ s) (hA : IsAntichain (· ≤ ·) (A : Set α))
    (hcard : A.card = n) {c : ℕ} (hc : c < n) : ∃ y ∈ A, f y = c := by
  have hinj : Set.InjOn f (A : Set α) := by
    intro a ha b hb hab
    have hab' := h.2 a (hAs ha) b (hAs hb) hab
    cases hab' with
    | inl h => by_contra hne; exact hA ha hb hne h
    | inr h => by_contra hne; exact hA hb ha (fun hab => hne hab.symm) h
  have hsubset : ∀ a ∈ A, f a ∈ Finset.range n := by
    exact fun a ha => Finset.mem_range.mpr (h.1 a (hAs ha))
  have hcard' : (Finset.image f A).card = n := by rw [Finset.card_image_of_injOn hinj, hcard]
  have heq : Finset.image f A = Finset.range n := by
    apply Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hsubset)
    rw [hcard', Finset.card_range]
  have hc' : c ∈ Finset.range n := Finset.mem_range.mpr hc
  rw [← heq] at hc'
  exact Finset.mem_image.mp hc'

omit [DecidableEq α] in
/-- A nonempty finite subset of a partial order contains a maximal element `a` together with a
minimal element `b ≤ a`. -/
