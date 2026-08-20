/-!
# Cassini 9
Category: Pure Mathematics
Target: Math.cassini_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, agreeing with `Nat.fib` from Mathlib
(`fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`). -/

theorem cassini_9_natFib :
    (Nat.fib 8 : ℤ) * (Nat.fib 10 : ℤ) - (Nat.fib 9 : ℤ) ^ 2 = (-1) ^ 9 := by
  norm_num

end Math

