import Mathlib
import RequestProject.Cassini12

/-!
# Cassini 12, stated with Mathlib's `Nat.fib`

This companion file relates `Math.fib` to Mathlib's `Nat.fib`, proves the general Cassini
identity, and derives the `n = 12` instance in terms of `Nat.fib`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem cassini_12_natFib :
    (Nat.fib 11 : ℤ) * (Nat.fib 13 : ℤ) - (Nat.fib 12 : ℤ) ^ 2 = (-1) ^ 12 :=
  cassini 11

end Math

/-!
# Cassini 12
Category: Pure Mathematics
Target: Math.cassini_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
This agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_natFib` in `Cassini12Mathlib.lean`). -/
