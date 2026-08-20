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

lemma height_lt_height {x y : α} (h : x < y) : height x < height y := by
  open Classical in
  obtain ⟨c, hc_chain, hc_le, hc_card⟩ := exists_chain_height x
  have hc_lt_y : ∀ z ∈ c, z < y := fun z hz => lt_of_le_of_lt (hc_le z hz) h
  -- Show y ∉ c (otherwise y ≤ x, contradicting x < y)
  have hy_notin_c : y ∉ c := fun hy => h.not_ge (hc_le y hy)
  -- Define c' = c ∪ {y}
  let c' : Finset α := {y} ∪ c
  have hc'_chain : IsChain (· ≤ ·) (c' : Set α) := by
    have hc'_coe : (c' : Set α) = ({y} : Set α) ∪ (c : Set α) := by simp [c']
    rw [hc'_coe]
    intro a ha b hb hab
    simp only [Set.mem_union, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | hac
    · rcases hb with rfl | hbc
      · exact absurd rfl hab
      · exact Or.inr (le_of_lt (hc_lt_y b hbc))
    · rcases hb with rfl | hbc
      · exact Or.inl (le_of_lt (hc_lt_y a hac))
      · exact hc_chain hac hbc hab
  have hc'_le : ∀ z ∈ c', z ≤ y := by
    intro z hz
    rw [Finset.mem_union, Finset.mem_singleton] at hz
    cases hz with
    | inl hz => exact hz ▸ le_refl y
    | inr hz => exact le_trans (hc_le z hz) (le_of_lt h)
  have hc'_card : c'.card = c.card + 1 := by
    show ({y} ∪ c).card = c.card + 1
    rw [Finset.card_union_of_disjoint (by simpa using hy_notin_c), Finset.card_singleton,
      Nat.add_comm]
  -- height y ≥ c'.card = c.card + 1 = height x + 1 > height x
  calc height x = c.card := hc_card.symm
    _ < c.card + 1 := Nat.lt_succ_self _
    _ = c'.card := hc'_card.symm
    _ ≤ height y := by
        apply Finset.le_sup (f := Finset.card) (hb := _)
        simp [hc'_chain]
        exact hc'_le

/-- If all chains have at most `n` elements, all heights are at most `n`. -/
