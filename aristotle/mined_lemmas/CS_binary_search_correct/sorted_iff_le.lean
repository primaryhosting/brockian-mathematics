import Mathlib
import RequestProject.Main

/-!
# Binary search correctness, specialised to a Mathlib `LinearOrder`

`CS.binary_search_correct` (in `RequestProject.Main`) is stated for an arbitrary decidable
strict order satisfying antisymmetry.  Here we record the corollary for any Mathlib
`LinearOrder`, where the antisymmetry hypothesis is automatic, and we phrase sortedness
using `≤`.
-/

namespace CS

variable {α : Type*} [LinearOrder α] [Inhabited α]

/-- Sortedness stated with `≤` agrees with `CS.Sorted`. -/

theorem sorted_iff_le (a : Array α) :
    Sorted a ↔ ∀ i j : Nat, i ≤ j → j < a.size → a[i]! ≤ a[j]! := by
  constructor
  · intro h i j hij hj
    exact not_lt.mp (h i j hij hj)
  · intro h i j hij hj
    exact not_lt.mpr (h i j hij hj)

/-- **Binary search is correct** over any linear order: on a sorted array, `binarySearch`
returns an index iff the key occurs in the array, and any returned index is a valid index
carrying the key. -/
