import Mathlib
import RequestProject.Cassini7

/-!
# Cassini 7, stated with Mathlib's `Nat.fib`

This file connects the self-contained Fibonacci definition `Math.fib` of
`RequestProject/Cassini7.lean` with Mathlib's `Nat.fib`, and restates Cassini's
identity at `n = 7` in terms of `Nat.fib`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem cassini_7_natFib :
    (Nat.fib 6 : ℤ) * (Nat.fib 8 : ℤ) - (Nat.fib 7 : ℤ) ^ 2 = (-1) ^ 7 := by
  simpa [fib_eq_natFib] using cassini_7

end Math

/-!
# Cassini 7
Category: Pure Mathematics
Target: Math.cassini_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
(Shown to agree with Mathlib's `Nat.fib` in `RequestProject/Cassini7Mathlib.lean`.) -/
