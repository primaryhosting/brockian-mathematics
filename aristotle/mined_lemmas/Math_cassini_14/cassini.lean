/-
Supplement to `RequestProject/Cassini14.lean`: identifies the Fibonacci sequence
`Math.fib` used there with Mathlib's `Nat.fib`, and restates Cassini 14 for `Nat.fib`.
-/
import Mathlib
import RequestProject.Cassini14

namespace Math


theorem cassini (n : Nat) :
    fib (n + 1) * fib (n + 3) - fib (n + 2) ^ 2 = (-1 : Int) ^ (n + 2) := by
  simpa [Int.pow_succ] using cassini_mul n

/-- Cassini's identity at `n = 14`: `F 13 * F 15 - F 14 ^ 2 = (-1) ^ 14`. -/
