/-!
# Cassini 2
Category: Pure Mathematics
Target: Math.cassini_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 2`: `F(1) * F(3) - F(2)^2 = (-1)^2`,
stated over the integers. -/
theorem cassini_2 :
    (fib 1 : Int) * (fib 3 : Int) - (fib 2 : Int) ^ 2 = (-1) ^ 2 := by
  decide

end Math

import Mathlib
import RequestProject.Main

/-!
# Cassini 2, connected to Mathlib's `Nat.fib`

This file records that the Fibonacci sequence used in `RequestProject.Main`
agrees with Mathlib's `Nat.fib`, and restates Cassini's identity at `n = 2`
in terms of `Nat.fib`.
-/

namespace Math

theorem fib_eq_natFib : ∀ n : Nat, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_natFib n, fib_eq_natFib (n + 1)]

/-- Cassini's identity at `n = 2` for Mathlib's `Nat.fib`. -/
theorem cassini_2_natFib :
    (Nat.fib 1 : ℤ) * (Nat.fib 3 : ℤ) - (Nat.fib 2 : ℤ) ^ 2 = (-1) ^ 2 := by
  simpa [fib_eq_natFib] using cassini_2

end Math

