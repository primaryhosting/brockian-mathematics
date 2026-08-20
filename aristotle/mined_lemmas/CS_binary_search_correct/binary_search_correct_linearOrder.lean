import Mathlib
import RequestProject.Main

/-!
# Binary search correctness, stated with Mathlib's `LinearOrder`

`CS.binary_search_correct` in `RequestProject/Main.lean` is stated using the Lean core
order classes `Std.IsLinearOrder` / `Std.LawfulOrderLT`. Mathlib's `LinearOrder`
provides both, so the statement specializes immediately, as recorded here.
-/

set_option autoImplicit false

namespace CS

universe u

/-- Binary search on a sorted array over a Mathlib `LinearOrder` returns an index
if and only if the key occurs in the array. -/

theorem binary_search_correct_linearOrder {α : Type u} [LinearOrder α] (a : Array α)
    (h : a.toList.Pairwise (· ≤ ·)) (k : α) :
    (binarySearch a k).isSome ↔ k ∈ a :=
  binary_search_correct a h k

/-- A sanity check: searching a sorted array of naturals. -/
example : binarySearch #[1, 3, 5, 7, 9] 7 = some 3 := by simp [binarySearch, bsearchAux]

/-- A sanity check: an absent key is not found. -/
example : binarySearch #[1, 3, 5, 7, 9] 4 = none := by simp [binarySearch, bsearchAux]

end CS

/-!
# Binary Search Correct
Category: Computer Science
Target: CS.binary_search_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the file layout: Lean does not allow a module docstring (`/-! ... -/`) to
precede `import` commands, so this module is written against the Lean core
prelude only (no `import` line at all).  Consequently the order-theoretic
typeclasses used below are the core ones (`Std.IsLinearOrder`,
`Std.LawfulOrderLT`), which Mathlib's `LinearOrder` instances provide
automatically; `RequestProject/LinearOrder.lean` records the Mathlib-flavoured
restatement `CS.binary_search_correct_linearOrder`.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

universe u

variable {α : Type u} [LE α] [LT α] [DecidableEq α] [DecidableLT α]
  [Std.IsLinearOrder α] [Std.LawfulOrderLT α]

/-- Binary search for `k` inside the slice `[lo, hi)` of the array `a`.
Returns `some i` when the key was found at index `i`, and `none` otherwise. -/
