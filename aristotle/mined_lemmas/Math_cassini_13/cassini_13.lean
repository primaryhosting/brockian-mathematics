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


theorem cassini_13 :
    (fib 12 : Int) * (fib 14 : Int) - (fib 13 : Int) ^ 2 = (-1) ^ 13 := by
  decide

end Math

