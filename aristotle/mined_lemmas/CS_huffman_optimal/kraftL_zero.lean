import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


@[simp] theorem kraftL_zero : kraftL 0 = 0 := rfl

