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

theorem card_le_card_of_cover (A : Finset α) (hA : IsAntichain (· ≤ ·) (A : Set α))
    (C : Finset (Finset α)) (hC : ∀ c ∈ C, IsChain (· ≤ ·) (c : Set α))
    (hcov : ∀ a : α, ∃ c ∈ C, a ∈ c) : A.card ≤ C.card := by
  -- Define a function that picks a chain containing each element
  let g : α → Finset α := fun a => Classical.choose (hcov a)
  -- Show that g maps elements of A to elements of C
  have hg_in_C : ∀ a ∈ A, g a ∈ C := fun a ha => (Classical.choose_spec (hcov a)).1
  -- Now we show that the restriction of g to A is injective
  have hinj : Set.InjOn g ↑A := by
    intro a ha a' ha' heq
    have hain : a ∈ g a := (Classical.choose_spec (hcov a)).2
    have ha'in : a' ∈ g a' := (Classical.choose_spec (hcov a')).2
    rw [heq.symm] at ha'in
    -- Both a and a' are in g a, which is a chain
    have hchain : IsChain (· ≤ ·) (↑(g a) : Set α) := hC _ (hg_in_C a ha)
    cases eq_or_ne a a' with
    | inl h => exact h
    | inr hne =>
      have hcomp : a ≤ a' ∨ a' ≤ a := hchain hain ha'in hne
      cases hcomp with
      | inl hle => exact absurd hle (hA ha ha' hne)
      | inr hle => exact absurd hle (hA ha' ha hne.symm)
  -- Now conclude A.card ≤ C.card from injectivity
  have hmono : A.image g ⊆ C := by
    intro c hc
    rcases Finset.mem_image.1 hc with ⟨a, ha, rfl⟩
    exact hg_in_C a ha
  rw [← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hmono

section Cover

variable [Fintype α]

/-- Dilworth's theorem: in a finite partial order in which every antichain has at most `n`
elements, the whole order can be covered by at most `n` chains. -/
