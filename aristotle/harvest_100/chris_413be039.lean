/-!
# Cassini 4
Category: Pure Mathematics
Target: Math.cassini_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
This agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_nat_fib` in
`RequestProject.CassiniMathlib`). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 4`: `F 3 * F 5 - F 4 ^ 2 = (-1) ^ 4`. -/
theorem cassini_4 :
    (fib 3 : Int) * (fib 5 : Int) - (fib 4 : Int) ^ 2 = (-1) ^ 4 := by
  decide

end Math

import Mathlib
import RequestProject.Main

/-!
# Cassini 4 — Mathlib cross-check

This file records that the Fibonacci sequence `Math.fib` used to state `Math.cassini_4`
coincides with Mathlib's `Nat.fib`, and restates Cassini's identity at `n = 4`
directly in terms of `Nat.fib`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1), Nat.fib_add_two]

/-- Cassini's identity at `n = 4`, stated with Mathlib's `Nat.fib`. -/
theorem cassini_4_nat_fib :
    (Nat.fib 3 : ℤ) * (Nat.fib 5 : ℤ) - (Nat.fib 4 : ℤ) ^ 2 = (-1) ^ 4 := by
  simpa [fib_eq_nat_fib] using Math.cassini_4

end Math

