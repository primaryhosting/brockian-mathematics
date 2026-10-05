import Mathlib
/-!
# Catalan Closed
Category: Pure Mathematics
Target: Math.catalan_closed
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The exact (division-free) form of the closed formula: `(n+1) * catalan n = C(2n, n)`. -/

theorem catalan_mul_succ (n : ℕ) : (n + 1) * catalan n = Nat.choose (2 * n) n := by
  rw [succ_mul_catalan_eq_centralBinom, Nat.centralBinom, two_mul]

/-- **Closed formula for the Catalan numbers**: the `n`-th Catalan number equals
`C(2n, n) / (n + 1)` (the division is exact). -/
