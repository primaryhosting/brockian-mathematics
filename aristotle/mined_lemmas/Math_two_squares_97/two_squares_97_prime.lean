import Mathlib
import RequestProject.TwoSquares97

/-!
# Two Squares 97, phrased with Mathlib's `Nat.Prime`

This file restates `Math.two_squares_97` using `Nat.Prime`.
-/

namespace Math

/-- The prime `97` is a sum of two squares: `97 = 4 ^ 2 + 9 ^ 2`. -/

theorem two_squares_97_prime : Nat.Prime 97 ∧ ∃ a b : ℕ, 97 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, two_squares_97.2⟩

end Math

/-!
# Two Squares 97
Category: Pure Mathematics
Target: Math.two_squares_97
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 97.** The number `97` is prime (it is at least `2` and its only
divisors are `1` and itself) and it is a sum of two squares, namely `97 = 4 ^ 2 + 9 ^ 2`.

The primality predicate is spelled out explicitly here so that the statement is
self-contained; `Math.two_squares_97_prime` in `RequestProject.TwoSquares97Mathlib`
records the same result phrased with Mathlib's `Nat.Prime`. -/
