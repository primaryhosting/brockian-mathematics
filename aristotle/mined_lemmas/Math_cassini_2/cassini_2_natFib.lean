/-!
# Cassini 2
Category: Pure Mathematics
Target: Math.cassini_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/

theorem cassini_2_natFib :
    (Nat.fib 1 : ℤ) * (Nat.fib 3 : ℤ) - (Nat.fib 2 : ℤ) ^ 2 = (-1) ^ 2 := by
  simpa [fib_eq_natFib] using cassini_2

end Math

