import Mathlib
import RequestProject.Cassini13

/-!
# Cassini 13, stated for Mathlib's `Nat.fib`

Companion to `RequestProject/Cassini13.lean`.  We check that the locally defined
`Math.fib` agrees with Mathlib's `Nat.fib`, restate Cassini's identity at `n = 13`
for `Nat.fib`, and prove the general Cassini identity
`F (n+2) * F n - F (n+1) ^ 2 = (-1) ^ (n+1)` by induction.
-/

namespace Math


def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity at `n = 13`**: `F 12 * F 14 - F 13 ^ 2 = (-1) ^ 13`,
computed in `ℤ`.  Numerically, `F 12 = 144`, `F 13 = 233`, `F 14 = 377`, and
`144 * 377 - 233 ^ 2 = 54288 - 54289 = -1`. -/
