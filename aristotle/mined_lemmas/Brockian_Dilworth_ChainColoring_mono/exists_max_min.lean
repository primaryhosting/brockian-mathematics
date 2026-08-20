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

lemma exists_max_min {s : Finset α} (hs : s.Nonempty) :
    ∃ a ∈ s, ∃ b ∈ s, b ≤ a ∧ (∀ x ∈ s, a ≤ x → x = a) ∧ (∀ x ∈ s, x ≤ b → x = b) := by
  classical
  obtain ⟨a, ha⟩ := hs
  obtain ⟨a', _, hmax⟩ := Finset.exists_le_maximal s ha
  set t := s.filter (fun x => x ≤ a') with ht
  have htne : t.Nonempty := ⟨a', by simp [ht, hmax.1]⟩
  obtain ⟨b, hmin⟩ := Finset.exists_minimal htne
  have hbt : b ∈ t := hmin.1
  have hbs : b ∈ s := (Finset.mem_filter.mp hbt).1
  refine ⟨a', hmax.1, b, hbs, (Finset.mem_filter.mp hbt).2, ?_, ?_⟩
  · intro x hx hx'
    exact le_antisymm (hmax.2 hx hx') hx'
  · intro x hx hxb
    exact le_antisymm hxb (hmin.2 (Finset.mem_filter.mpr
      ⟨hx, hxb.trans (Finset.mem_filter.mp hbt).2⟩) hxb)

/-- Key comparability lemma: if `x` lies below the antichain `A`, `x'` lies above `A`, and both
are comparable with the same element `y ∈ A`, then `x` and `x'` are comparable. -/
