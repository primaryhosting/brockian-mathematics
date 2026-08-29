import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


@[simp] theorem cost_leaf (w : α → ℝ) (a : α) : (leaf a).cost w = 0 := rfl
