/-
Supplement to `RequestProject/Cassini14.lean`: identifies the Fibonacci sequence
`Math.fib` used there with Mathlib's `Nat.fib`, and restates Cassini 14 for `Nat.fib`.
-/
import Mathlib
import RequestProject.Cassini14

namespace Math


@[simp] theorem fib_one : fib 1 = 1 := rfl

