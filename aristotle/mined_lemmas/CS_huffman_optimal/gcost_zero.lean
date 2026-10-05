import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


@[simp] theorem gcost_zero (C W : β → ℝ) : gcost C W (0 : Multiset (β × ℕ)) = 0 := rfl

/-- Rearranging the lengths so that the two lightest items `b1, b2` carry the two largest
lengths does not increase the cost. -/
