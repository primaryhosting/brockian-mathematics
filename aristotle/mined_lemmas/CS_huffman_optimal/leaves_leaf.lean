import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


@[simp] theorem leaves_leaf (a : α) : (leaf a).leaves = {a} := rfl
