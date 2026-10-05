import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


@[simp] theorem encode_leaf [DecidableEq α] (b a : α) : (leaf b).encode a = [] := rfl

