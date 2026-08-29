/-!
# Cassini 11
Category: Pure Mathematics
Target: Math.cassini_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`,
`fib (n + 2) = fib n + fib (n + 1)`. -/

theorem cassini_11_nat_fib :
    (Nat.fib 10 : ℤ) * (Nat.fib 12 : ℤ) - (Nat.fib 11 : ℤ) ^ 2 = (-1) ^ 11 := by
  simpa only [fib_eq_nat_fib] using cassini_11

end Math

