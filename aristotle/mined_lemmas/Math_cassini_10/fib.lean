/-!
# Cassini 10
Category: Pure Mathematics
Target: Math.cassini_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
This matches `Nat.fib` from Mathlib (see `Math.fib_eq_natFib` in `RequestProject.Cassini10Fib`). -/

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 10`: `F(9) * F(11) - F(10)^2 = (-1)^10`. -/
