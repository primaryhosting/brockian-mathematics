/-
Supplement to `RequestProject/Cassini14.lean`: identifies the Fibonacci sequence
`Math.fib` used there with Mathlib's `Nat.fib`, and restates Cassini 14 for `Nat.fib`.
-/
import Mathlib
import RequestProject.Cassini14

namespace Math


def fib : Nat → Int
  | 0 => 0
  | 1 => 1
  | (n + 2) => fib n + fib (n + 1)

