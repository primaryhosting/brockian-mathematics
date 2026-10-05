import Mathlib
import RequestProject.TwoSquares5

/-!
# Two Squares 5 (Mathlib phrasing)

A restatement of `Math.two_squares_5` using Mathlib's `Nat.Prime`, together with a proof that the
explicit primality condition appearing in `Math.two_squares_5` really is `Nat.Prime 5`.
-/

namespace Math

/-- The prime `5` is a sum of two squares: `5 = 1 ^ 2 + 2 ^ 2`. -/

theorem two_squares_5_nat_prime : Nat.Prime 5 ∧ ∃ a b : ℕ, 5 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 1, 2, by norm_num⟩

/-- The explicit primality condition used in `Math.two_squares_5` is exactly `Nat.Prime 5`. -/
