import Mathlib
import RequestProject.TwoSquares109

/-!
# Two Squares 109 (Mathlib phrasing)

Restatements of `Math.two_squares_109` using Mathlib's `Nat.Prime`, together with
the check that the elementary primality condition used in `Math.two_squares_109`
is exactly `Nat.Prime 109`.
-/

namespace Math

/-- The elementary primality condition appearing in `Math.two_squares_109`
(`2 ≤ n` and every divisor of `n` is `1` or `n`) is equivalent to `Nat.Prime n`. -/

theorem nat_prime_iff_elementary (n : ℕ) :
    Nat.Prime n ↔ (2 ≤ n ∧ ∀ m : ℕ, m ∣ n → m = 1 ∨ m = n) :=
  Nat.prime_def

/-- The prime `109` is a sum of two squares, phrased with Mathlib's `Nat.Prime`. -/
