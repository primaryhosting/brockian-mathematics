/-
# Catalan Closed
Category: Pure Mathematics
Target: Math.catalan_closed
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

namespace Math

/-- The `n`th Catalan number equals `C(2n, n) / (n+1)` (exact natural division,
since `n + 1` divides the central binomial coefficient). -/

theorem succ_dvd_choose_two_mul (n : ℕ) : (n + 1) ∣ (2 * n).choose n :=
  Nat.succ_dvd_centralBinom n

/-- Rational form of the closed formula: `catalan n = C(2n,n) / (n+1)` in `ℚ`. -/
