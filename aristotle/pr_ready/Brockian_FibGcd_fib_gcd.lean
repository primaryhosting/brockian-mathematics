/-!
# Fib Gcd
Category: Brockian External
Target: Brockian.FibGcd.fib_gcd
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.FibGcd
/-- Fibonacci strong divisibility: gcd(F_m, F_n) = F_{gcd(m,n)}. -/
theorem fib_gcd (m n : ℕ) :
    Nat.fib (Nat.gcd m n) = Nat.gcd (Nat.fib m) (Nat.fib n) := by
  exact Nat.fib_gcd m n
end Brockian.FibGcd

