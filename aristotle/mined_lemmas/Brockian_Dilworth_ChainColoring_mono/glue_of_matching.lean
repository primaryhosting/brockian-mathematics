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

lemma glue_of_matching {s D U A : Finset α} {n : ℕ} {fD fU : α → ℕ} {g : ℕ → α}
    (hA : IsAntichain (· ≤ ·) (A : Set α)) (hAD : A ⊆ D) (hAU : A ⊆ U)
    (hsub : ∀ x ∈ s, x ∈ D ∨ x ∈ U)
    (hD : ∀ x ∈ D, ∃ y ∈ A, x ≤ y) (hU : ∀ x ∈ U, ∃ y ∈ A, y ≤ x)
    (hfD : ChainColoring D n fD) (hfU : ChainColoring U n fU)
    (hg : ∀ c < n, g c ∈ A ∧ fU (g c) = c) :
    ChainColoring s n (fun x => if x ∈ D then fD x else fD (g (fU x))) := by
  classical
  refine ⟨?_, ?_⟩
  · intro x hx
    by_cases hxD : x ∈ D
    · simpa only [if_pos hxD] using hfD.1 x hxD
    · have hxU : x ∈ U := (hsub x hx).resolve_left hxD
      have hc : fU x < n := hfU.1 x hxU
      simpa only [if_neg hxD] using hfD.1 _ (hAD (hg _ hc).1)
  · intro x hx x' hx' heq
    by_cases hxD : x ∈ D <;> by_cases hx'D : x' ∈ D
    · simp only [if_pos hxD, if_pos hx'D] at heq
      exact hfD.2 x hxD x' hx'D heq
    · simp only [if_pos hxD, if_neg hx'D] at heq
      have hx'U : x' ∈ U := (hsub x' hx').resolve_left hx'D
      exact glue_mixed hA hAD hAU hD hU hfD hfU hg hxD hx'U heq
    · simp only [if_neg hxD, if_pos hx'D] at heq
      have hxU : x ∈ U := (hsub x hx).resolve_left hxD
      exact (glue_mixed hA hAD hAU hD hU hfD hfU hg hx'D hxU heq.symm).symm
    · simp only [if_neg hxD, if_neg hx'D] at heq
      exact glue_upper hA hAD hfD hfU hg ((hsub x hx).resolve_left hxD)
        ((hsub x' hx').resolve_left hx'D) heq

/-- Gluing step: if `s` is contained in the union of a "lower part" `D` and an "upper part" `U`,
both of which are `n`-coloured and both of which contain the antichain `A` of size `n`, then `s`
admits an `n`-colouring. -/
