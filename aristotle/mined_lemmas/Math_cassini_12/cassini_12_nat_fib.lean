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

theorem cassini_12_nat_fib :
    (Nat.fib 11 : ℤ) * (Nat.fib 13 : ℤ) - (Nat.fib 12 : ℤ) ^ 2 = (-1 : ℤ) ^ 12 := by
  norm_num [Nat.fib]

/-- The general Cassini identity: `F(n) * F(n+2) - F(n+1)^2 = (-1)^(n+1)`. -/
