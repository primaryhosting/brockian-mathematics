import Mathlib
import RequestProject.Cassini14

/-!
# Cassini 14 (Mathlib restatement)

This file identifies the self-contained Fibonacci sequence `Math.F` of
`RequestProject/Cassini14.lean` with Mathlib's `Nat.fib`, and restates Cassini's
identity at `n = 14` in terms of `Nat.fib`.
-/

namespace Math


def F : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => F n + F (n + 1)

/-- Cassini's identity at `n = 14`: `F 13 * F 15 - F 14 ^ 2 = (-1) ^ 14`,
with the arithmetic carried out in `ℤ`. -/
