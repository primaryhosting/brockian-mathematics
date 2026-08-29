import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem buildList_of_le (w : α → ℝ) {ts : List (HTree α)} (h : 2 ≤ ts.length) :
    buildList w ts = buildList w (combineStep w ts) := by
  rw [buildList]
  simp [h]

/-- The total cost of a list of trees. -/
