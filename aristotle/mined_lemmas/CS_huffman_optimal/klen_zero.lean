import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


@[simp] theorem klen_zero : klen (0 : Multiset (β × ℕ)) = 0 := rfl

/-- Total cost of a length assignment: each item `b` contributes a fixed amount `C b`
plus its weight `W b` times the length assigned to it. -/
