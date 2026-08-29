import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


@[simp] theorem wt_node (w : α → ℝ) (l r : HTree α) :
    (node l r).wt w = l.wt w + r.wt w := rfl

/-- The cost (weighted external path length) of a tree. -/
