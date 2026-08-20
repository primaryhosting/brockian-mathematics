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

theorem catalan_closed (n : ℕ) : catalan n = (2 * n).choose n / (n + 1) := by
  simpa [Nat.centralBinom] using catalan_eq_centralBinom_div n

/-- Divisibility making the natural-number division in `catalan_closed` exact. -/
