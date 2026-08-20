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

noncomputable def height {α : Type*} [Fintype α] [PartialOrder α] (x : α) : ℕ :=
  (Finset.univ.filter
      (fun c : Finset α => IsChain (· ≤ ·) (c : Set α) ∧ ∀ y ∈ c, y ≤ x)).sup Finset.card

variable {α : Type*} [Fintype α] [PartialOrder α]

open Classical in
/-- The set of chains below `x`, over which the height is a supremum, is nonempty. -/

lemma height_filter_nonempty (x : α) :
    (Finset.univ.filter
      (fun c : Finset α => IsChain (· ≤ ·) (c : Set α) ∧ ∀ y ∈ c, y ≤ x)).Nonempty := by
  use ∅
  simp [IsChain]

/-- The height of `x` is realised by an actual chain below `x`. -/
