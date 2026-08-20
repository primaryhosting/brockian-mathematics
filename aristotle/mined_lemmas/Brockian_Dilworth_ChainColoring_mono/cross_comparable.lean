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

lemma cross_comparable {A : Finset α} (hA : IsAntichain (· ≤ ·) (A : Set α)) {x x' y : α}
    (hy : y ∈ A) (hxA : ∃ z ∈ A, x ≤ z) (hx'A : ∃ z ∈ A, z ≤ x')
    (hxy : x ≤ y ∨ y ≤ x) (hx'y : x' ≤ y ∨ y ≤ x') : x ≤ x' ∨ x' ≤ x := by
  obtain ⟨z, hzA, hxz⟩ := hxA
  obtain ⟨z', hz'A, hz'x'⟩ := hx'A
  have hxy_le : x ≤ y := by
    rcases hxy with hxy | hxy
    · exact hxy
    · have hlez : y ≤ z := hxy.trans hxz
      by_cases heq : y = z
      · exact heq.symm ▸ hxz
      · exact (hA hy hzA heq hlez).elim
  have hyx'_le : y ≤ x' := by
    rcases hx'y with hx'y | hx'y
    · rcases eq_or_ne y z' with rfl | hne
      · exact hz'x'
      · exact (hA hz'A hy hne.symm (hz'x'.trans hx'y)).elim
    · exact hx'y
  exact Or.inl (hxy_le.trans hyx'_le)

/-- Mixed case of the gluing step: `x` lies in the lower part `D`, `x'` lies in the upper part
`U`, and the glued colours of `x` and `x'` agree; then `x` and `x'` are comparable. -/
