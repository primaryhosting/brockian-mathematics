import Mathlib
import RequestProject.Cassini4

/-!
# Cassini 4, phrased with Mathlib's `Nat.fib`
-/

namespace Math

/-- The locally defined Fibonacci sequence agrees with Mathlib's `Nat.fib`. -/

def F : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => F n + F (n + 1)

/-- Cassini's identity at `n = 4`: `F 3 * F 5 - F 4 ^ 2 = (-1) ^ 4`. -/
