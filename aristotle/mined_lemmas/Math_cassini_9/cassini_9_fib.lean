/-!
# Cassini 9
Category: Pure Mathematics
Target: Math.cassini_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, valued in `ℤ`: `fibZ 0 = 0`, `fibZ 1 = 1`,
`fibZ (n + 2) = fibZ n + fibZ (n + 1)`. -/

theorem cassini_9_fib :
    (Nat.fib 8 : Int) * (Nat.fib 10 : Int) - (Nat.fib 9 : Int) ^ 2 = (-1) ^ 9 := by
  simpa [fibZ_eq_fib] using cassini_9

end Math

