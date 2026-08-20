import Mathlib

/-!
# Two Squares 109 (Mathlib version)

Mathlib-based companion to `RequestProject/TwoSquares109.lean`: the prime `109`
is a sum of two squares, both by an explicit witness and via Mathlib's
`Nat.Prime.sq_add_sq` (Fermat's theorem on sums of two squares).
-/

namespace Math

/-- `109` is prime and `109 = 10 ^ 2 + 3 ^ 2`. -/

theorem two_squares_109_mathlib : Nat.Prime 109 ∧ ∃ a b : ℕ, a ^ 2 + b ^ 2 = 109 :=
  ⟨by norm_num, 10, 3, by norm_num⟩

/-- The existence part obtained abstractly from `Nat.Prime.sq_add_sq`, which applies
since `109` is prime and `109 % 4 = 1 ≠ 3`. -/
