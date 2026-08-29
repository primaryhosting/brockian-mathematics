import Mathlib
import RequestProject.Math

/-!
# Cassini 3, stated with Mathlib's `Nat.fib`

This file links the self-contained `Math.fib` used in `RequestProject.Math` with
Mathlib's `Nat.fib`, and restates Cassini's identity at `n = 3` for `Nat.fib`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem cassini_3_nat_fib :
    (Nat.fib 2 : Int) * (Nat.fib 4 : Int) - (Nat.fib 3 : Int) ^ 2 = (-1) ^ 3 := by
  simp only [← fib_eq_nat_fib]
  exact cassini_3

end Math

/-!
# Cassini 3
Category: Pure Mathematics
Target: Math.cassini_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
This agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_nat_fib` in `RequestProject.MathFib`). -/
