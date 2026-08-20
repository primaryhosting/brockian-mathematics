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

lemma glue_upper {D U A : Finset α} {n : ℕ} {fD fU : α → ℕ} {g : ℕ → α}
    (hA : IsAntichain (· ≤ ·) (A : Set α)) (hAD : A ⊆ D)
    (hfD : ChainColoring D n fD) (hfU : ChainColoring U n fU)
    (hg : ∀ c < n, g c ∈ A ∧ fU (g c) = c)
    {x x' : α} (hxU : x ∈ U) (hx'U : x' ∈ U) (heq : fD (g (fU x)) = fD (g (fU x'))) :
    x ≤ x' ∨ x' ≤ x := by
  -- Let c = fU x and c' = fU x'
  have hc : fU x < n := hfU.1 x hxU
  have hc' : fU x' < n := hfU.1 x' hx'U
  -- g (fU x) and g (fU x') are in A
  have hgxc : g (fU x) ∈ A := (hg _ hc).1
  have hgxc' : g (fU x') ∈ A := (hg _ hc').1
  -- Since fD is a chain coloring on D and both are in D, they're comparable
  have hcomp : g (fU x) ≤ g (fU x') ∨ g (fU x') ≤ g (fU x) :=
    hfD.2 (g (fU x)) (hAD hgxc) (g (fU x')) (hAD hgxc') heq
  -- But A is an antichain, so they must be equal
  have heqe : g (fU x) = g (fU x') := by
    rcases hcomp with hle | hle
    · exact Classical.byContradiction fun hne => hA hgxc hgxc' hne hle
    · exact Classical.byContradiction fun hne => hA hgxc' hgxc (Ne.symm hne) hle
  -- Since fU (g c) = c for all c < n, we have fU x = fU x'
  have hfUxeq : fU (g (fU x)) = fU x := (hg _ hc).2
  have hfUx'e : fU (g (fU x')) = fU x' := (hg _ hc').2
  have hfUeq : fU x = fU x' := by rw [← hfUxeq, ← hfUx'e, heqe]
  -- Now use hfU to conclude comparability
  exact hfU.2 x hxU x' hx'U hfUeq

/-- Gluing step, with the colour-matching function `g` given: `g c` picks out the element of the
antichain `A` with `fU`-colour `c`, and the glued colouring recolours an upper element `x` with
the `fD`-colour of the antichain element matching it. -/
