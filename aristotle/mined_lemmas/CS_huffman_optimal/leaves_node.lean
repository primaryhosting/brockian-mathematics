import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


@[simp] theorem leaves_node (l r : HTree α) : (node l r).leaves = l.leaves + r.leaves := rfl

/-- The total weight of a tree. -/
