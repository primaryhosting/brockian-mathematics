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

theorem getElem_le_getElem_of_pairwise {a : Array α} (h : a.toList.Pairwise (· ≤ ·))
    {i j : Nat} (hi : i < a.size) (hj : j < a.size) (hij : i ≤ j) : a[i] ≤ a[j] := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact Std.IsPreorder.le_refl _
  · have := (List.pairwise_iff_getElem.mp h) i j (by simpa using hi) (by simpa using hj) hlt
    simpa using this

omit [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α] in
/-- Soundness: whenever `bsearchAux` returns an index, that index holds the key. -/
