import Mathlib
import RequestProject.TwoSquares29

/-!
# Two Squares 29 (Mathlib restatement)

A restatement of `Math.two_squares_29` using Mathlib's `Nat.Prime`.
-/

namespace Math

/-- The prime `29` is a sum of two squares: `29 = 2 ^ 2 + 5 ^ 2`. -/

theorem two_squares_29_prime : Nat.Prime 29 ∧ ∃ a b : ℕ, 29 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, two_squares_29.2⟩

end Math

/-!
# Two Squares 29
Category: Pure Mathematics
Target: Math.two_squares_29
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/--
**Two squares for 29.**

`29` is a prime number (spelled out elementarily: it is greater than `1` and its only
natural-number divisors are `1` and itself) and it is a sum of two squares,
namely `29 = 2 ^ 2 + 5 ^ 2`.

The header comment above must be the very first thing in this file, and Lean requires
`import` commands to precede any module documentation, so this file is deliberately
self-contained and uses only the Lean core library.  A Mathlib-flavoured restatement,
phrased with `Nat.Prime`, is provided in `RequestProject/TwoSquares29Mathlib.lean`.
-/
