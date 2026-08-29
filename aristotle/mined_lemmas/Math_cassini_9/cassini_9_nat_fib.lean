/-!
# Cassini 9
Category: Pure Mathematics
Target: Math.cassini_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
(Defined here rather than taken from Mathlib because the required file header is a module
docstring, which Lean requires to precede any `import` command; the file
`RequestProject/CassiniMathlib.lean` proves this agrees with `Nat.fib` and restates the
result in Mathlib terms.) -/

theorem cassini_9_nat_fib :
    (Nat.fib 8 : ℤ) * (Nat.fib 10 : ℤ) - (Nat.fib 9 : ℤ) ^ 2 = (-1) ^ 9 := by
  simpa [fib_eq_nat_fib] using cassini_9

end Math

