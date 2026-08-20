import Mathlib
namespace Brockian.MsMirsky

/-!
# Mirsky's theorem (dual Dilworth)

The original statement in this file asked for a family `A : Finset (Finset α)` of antichains
with `A.card = n` exactly.  That is not provable: a `Finset (Finset α)` consists of *distinct*
antichains, and there simply may not be `n` of them.  For instance with `α = Unit` and `n = 5`
the chain hypothesis holds (every chain has at most one element), yet
`Fintype.card (Finset (Finset Unit)) = 4 < 5`, so no `A` of cardinality `5` exists at all.

The statement below is therefore the standard form of Mirsky's theorem: the poset is covered by
*at most* `n` antichains (`A.card ≤ n`).  The mathematical content — "if all chains have size
at most `n`, then the poset is a union of `n` antichains" — is unchanged.  The original, false,
statement is kept commented out at the end of the file.

The proof uses the height function `height x`, the maximal cardinality of a chain contained in
`{y | y ≤ x}`; the level sets of `height` are antichains, and there are at most `n` of them.
-/

open Classical in
/-- The *height* of `x`: the maximal cardinality of a chain all of whose elements are `≤ x`. -/

lemma exists_chain_height (x : α) :
    ∃ c : Finset α, IsChain (· ≤ ·) (c : Set α) ∧ (∀ y ∈ c, y ≤ x) ∧ c.card = height x := by
  open Classical in
  set S := Finset.univ.filter (fun c : Finset α => IsChain (· ≤ ·) (c : Set α) ∧ ∀ y ∈ c, y ≤ x) with hS
  have hne : S.Nonempty := height_filter_nonempty x
  unfold height
  let S' := S.image Finset.card
  have hne' : S'.Nonempty := ⟨_, Finset.mem_image_of_mem _ (hne.choose_spec)⟩
  let m := S'.max' hne'
  have hm_in_S' : m ∈ S' := Finset.max'_mem S' hne'
  obtain ⟨c, hc_mem, hc_card⟩ := Finset.mem_image.mp hm_in_S'
  use c
  simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hc_mem ⊢
  refine ⟨hc_mem.1, hc_mem.2, ?_⟩
  rw [hc_card]
  unfold m S'
  rw [Finset.max'_eq_sup', Finset.sup'_eq_sup hne', Finset.sup_image]
  rfl

/-- Every element has positive height, witnessed by the singleton chain `{x}`. -/
