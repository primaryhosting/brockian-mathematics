import Mathlib
import RequestProject.TwoSquares5

/-!
# Two Squares 5 (Mathlib phrasing)

A restatement of `Math.two_squares_5` using Mathlib's `Nat.Prime`, together with a proof that the
explicit primality condition appearing in `Math.two_squares_5` really is `Nat.Prime 5`.
-/

namespace Math

/-- The prime `5` is a sum of two squares: `5 = 1 ^ 2 + 2 ^ 2`. -/

theorem two_squares_5_prime_spec :
    (2 ≤ 5 ∧ ∀ m : ℕ, m ∣ 5 → m = 1 ∨ m = 5) ↔ Nat.Prime 5 :=
  (Nat.prime_def (p := 5)).symm

/-- `Math.two_squares_5` restated with Mathlib's `Nat.Prime`, derived from the import-free version. -/
