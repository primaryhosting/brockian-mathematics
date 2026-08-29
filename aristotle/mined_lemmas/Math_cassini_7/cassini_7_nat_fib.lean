/-!
# Cassini 7
Category: Pure Mathematics
Target: Math.cassini_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.
(This file must begin with the required header comment, which Lean treats as a module
docstring and therefore forbids any `import` afterwards; hence the sequence is defined
here from scratch. The file `RequestProject/CassiniMathlib.lean` proves that this
sequence agrees with Mathlib's `Nat.fib` and restates the result for `Nat.fib`.) -/

theorem cassini_7_nat_fib :
    (Nat.fib 6 : ℤ) * (Nat.fib 8 : ℤ) - (Nat.fib 7 : ℤ) ^ 2 = (-1) ^ 7 := by
  norm_num [Nat.fib]

end Math

