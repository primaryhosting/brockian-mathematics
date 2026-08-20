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

theorem binary_search_sound (a : Array α) (k : α) {i : Nat} (hi : binarySearch a k = some i) :
    ∃ h : i < a.size, a[i] = k :=
  bsearchAux_sound a k 0 a.size i hi

/-- **Binary search is correct**: on a sorted array, binary search returns an index
if and only if the key is present in the array. -/
