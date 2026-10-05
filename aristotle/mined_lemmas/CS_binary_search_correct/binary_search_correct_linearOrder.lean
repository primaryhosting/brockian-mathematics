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

theorem binary_search_correct_linearOrder (a : Array α)
    (hs : ∀ i j : Nat, i ≤ j → j < a.size → a[i]! ≤ a[j]!) (key : α) :
    (∀ i : Nat, binarySearch a key = some i → i < a.size ∧ a[i]! = key) ∧
      ((∃ i : Nat, binarySearch a key = some i) ↔ ∃ i : Nat, i < a.size ∧ a[i]! = key) :=
  binary_search_correct (fun _ _ h1 h2 => le_antisymm (not_lt.mp h2) (not_lt.mp h1)) a
    ((sorted_iff_le a).mpr hs) key

/-- A concrete sanity check. -/
example : binarySearch #[1, 3, 5, 7, 9] 7 = some 3 := by
  simp [binarySearch, bsearchAux]

example : binarySearch #[1, 3, 5, 7, 9] 4 = none := by
  simp [binarySearch, bsearchAux]

end CS

/-!
# Binary Search Correct
Category: Computer Science
Target: CS.binary_search_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-!
## Setup

We work with an arbitrary type `α` carrying a decidable strict order `<`.  The only order
property that binary search needs is antisymmetry in the form

`∀ x y, ¬ x < y → ¬ y < x → x = y`,

which holds in any linear order; it is supplied as an explicit hypothesis so that the
development is independent of any particular order-class hierarchy.
-/

variable {α : Type u} [LT α] [DecidableLT α] [Inhabited α]

/-- An array is sorted when its entries are non-decreasing, i.e. `a[i]! ≤ a[j]!` for `i ≤ j`,
expressed with the strict order as `¬ a[j]! < a[i]!`. -/
