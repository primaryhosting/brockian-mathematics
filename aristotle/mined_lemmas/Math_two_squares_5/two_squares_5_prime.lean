import Mathlib
import RequestProject.TwoSquares5

/-!
# Two Squares 5 — Mathlib phrasing

The statement of `Math.two_squares_5` phrased with Mathlib's `Nat.Prime`, together with the
derivation of the Mathlib phrasing from the elementary one.
-/

namespace Math

/-- The prime `5` is a sum of two squares, phrased with Mathlib's `Nat.Prime`. -/

theorem two_squares_5_prime : Nat.Prime 5 ∧ ∃ a b : ℕ, 5 = a ^ 2 + b ^ 2 := by
  obtain ⟨⟨h1, hdvd⟩, hsq⟩ := two_squares_5
  exact ⟨Nat.prime_def.mpr ⟨h1, hdvd⟩, hsq⟩

end Math

/-!
# Two Squares 5
Category: Pure Mathematics
Target: Math.two_squares_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **The prime 5 is a sum of two squares.**

The number `5` is prime (it is greater than `1` and its only divisors are `1` and `5`)
and it is a sum of two squares, namely `5 = 1 ^ 2 + 2 ^ 2`.

(The primality predicate is spelled out explicitly here rather than via `Nat.Prime`, since
the required file header must be the first command in the file, which precludes an `import`
line; the equivalent statement phrased with Mathlib's `Nat.Prime` is
`Math.two_squares_5_prime` in `RequestProject/TwoSquares5Mathlib.lean`.) -/
