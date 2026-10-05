import Mathlib
/-!
# Catalan Closed
Category: Pure Mathematics
Target: Math.catalan_closed
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The `n`-th Catalan number equals `C(2n, n) / (n + 1)` (natural division, which is exact
here since `n + 1` divides the central binomial coefficient).
This is Mathlib's `catalan_eq_centralBinom_div`, with `Nat.centralBinom n = (2 * n).choose n`
unfolded. -/

theorem succ_mul_catalan_closed (n : ℕ) : (n + 1) * catalan n = Nat.choose (2 * n) n :=
  succ_mul_catalan_eq_centralBinom n

/-- Rational form of the closed formula: `catalan n = C(2n, n) / (n + 1)` in `ℚ`. -/
