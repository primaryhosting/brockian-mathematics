import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem buildList_of_lt (w : α → ℝ) {ts : List (HTree α)} (h : ts.length < 2) :
    buildList w ts = ts := by
  rw [buildList]
  simp [Nat.not_le.2 h]

