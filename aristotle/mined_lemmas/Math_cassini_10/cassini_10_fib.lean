/-!
# Cassini 10
Category: Pure Mathematics
Target: Math.cassini_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.
(Defined here rather than imported, since the required file header must be the
very first thing in the file, which rules out an `import` line.) -/

theorem cassini_10_fib :
    (Nat.fib 9 : Int) * (Nat.fib 11 : Int) - (Nat.fib 10 : Int) ^ 2 = (-1) ^ 10 := by
  simpa [F_eq_fib] using cassini_10

end Math

