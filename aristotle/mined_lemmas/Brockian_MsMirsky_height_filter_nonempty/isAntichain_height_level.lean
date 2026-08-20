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

lemma isAntichain_height_level [DecidableEq α] (k : ℕ) :
    IsAntichain (· ≤ ·) ((Finset.univ.filter (fun x : α => height x = k) : Finset α) : Set α) := by
  intro a ha b hb hab hle
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have hlt : a < b := hab.lt_of_le hle
  linarith [height_lt_height hlt]

/-- **Mirsky's theorem** (dual of Dilworth): if every chain in a finite poset has size `≤ n`,
    then the poset can be covered by (at most) `n` antichains. -/
