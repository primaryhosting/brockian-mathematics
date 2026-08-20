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

lemma glue_mixed {D U A : Finset α} {n : ℕ} {fD fU : α → ℕ} {g : ℕ → α}
    (hA : IsAntichain (· ≤ ·) (A : Set α)) (hAD : A ⊆ D) (hAU : A ⊆ U)
    (hD : ∀ x ∈ D, ∃ y ∈ A, x ≤ y) (hU : ∀ x ∈ U, ∃ y ∈ A, y ≤ x)
    (hfD : ChainColoring D n fD) (hfU : ChainColoring U n fU)
    (hg : ∀ c < n, g c ∈ A ∧ fU (g c) = c)
    {x x' : α} (hxD : x ∈ D) (hx'U : x' ∈ U) (heq : fD x = fD (g (fU x'))) :
    x ≤ x' ∨ x' ≤ x := by
  -- Let y = g(fU x') ∈ A
  have hc : fU x' < n := hfU.1 x' hx'U
  have hgx' : g (fU x') ∈ A := (hg _ hc).1
  -- Apply cross_comparable
  apply cross_comparable hA hgx'
  · exact hD x hxD
  · exact hU x' hx'U
  · -- Need to show x ≤ g(fU x') ∨ g(fU x') ≤ x
    exact hfD.2 x hxD (g (fU x')) (hAD hgx') heq
  · -- Need to show x' ≤ g(fU x') ∨ g(fU x') ≤ x'
    have hgcolour : fU (g (fU x')) = fU x' := (hg _ hc).2
    exact hfU.2 x' hx'U (g (fU x')) (hAU hgx') hgcolour.symm

omit [DecidableEq α] in
/-- Upper case of the gluing step: both `x` and `x'` lie in the upper part `U` and their glued
colours agree; then `x` and `x'` are comparable. -/
