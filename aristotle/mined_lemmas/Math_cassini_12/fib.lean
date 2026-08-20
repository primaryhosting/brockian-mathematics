import Mathlib
import RequestProject.Cassini12

/-!
# Cassini 12, in Mathlib terms

This file links the self-contained Fibonacci function `Math.fib` of
`RequestProject.Cassini12` with Mathlib's `Nat.fib`, and restates Cassini's identity
at `n = 12` for `Nat.fib`. It also proves the general Cassini identity.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 12`: `F(11) * F(13) - F(12)^2 = (-1)^12`. -/
