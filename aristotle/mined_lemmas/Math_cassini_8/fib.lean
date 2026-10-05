import Mathlib
import RequestProject.Main

/-!
# Bridge to Mathlib's `Nat.fib`

`Math.fib` (defined in `RequestProject.Main` without imports, as required by the
file header there) agrees with Mathlib's `Nat.fib`, so `Math.cassini_8` is a
statement about the usual Fibonacci numbers.
-/

namespace Math


def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 8`: `F(7) * F(9) - F(8)^2 = (-1)^8`. -/
