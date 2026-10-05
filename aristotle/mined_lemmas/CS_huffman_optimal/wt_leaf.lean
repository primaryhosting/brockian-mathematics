import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


@[simp] theorem wt_leaf (w : α → ℝ) (a : α) : (leaf a).wt w = w a := rfl
