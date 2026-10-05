import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


@[simp] theorem cost_node (w : α → ℝ) (l r : HTree α) :
    (node l r).cost w = l.cost w + r.cost w + l.wt w + r.wt w := rfl

