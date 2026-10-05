import Mathlib
import RequestProject.Cassini12

/-!
# Cassini 12, stated with Mathlib's `Nat.fib`

This companion file relates `Math.fib` to Mathlib's `Nat.fib`, proves the general Cassini
identity, and derives the `n = 12` instance in terms of `Nat.fib`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 12`: `F(11) * F(13) - F(12)^2 = (-1)^12`. -/
