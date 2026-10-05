/-!
# Cassini 7
Category: Pure Mathematics
Target: Math.cassini_7
Statement: Cassini: F(6)·F(8) − F(7)² = (−1)^7.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- Cassini's identity at n = 7: F(6)·F(8) − F(7)² = (−1)^7. -/
theorem cassini_7 :
    (Nat.fib 6 : ℤ) * (Nat.fib 8 : ℤ) - (Nat.fib 7 : ℤ) ^ 2 = (-1) ^ 7 := by
  norm_num [Nat.fib]

end Math

