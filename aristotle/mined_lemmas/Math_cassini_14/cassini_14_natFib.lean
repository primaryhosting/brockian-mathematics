/-
Supplement to `RequestProject/Cassini14.lean`: identifies the Fibonacci sequence
`Math.fib` used there with Mathlib's `Nat.fib`, and restates Cassini 14 for `Nat.fib`.
-/
import Mathlib
import RequestProject.Cassini14

namespace Math


theorem cassini_14_natFib :
    (Nat.fib 13 : Int) * (Nat.fib 15 : Int) - (Nat.fib 14 : Int) ^ 2 = (-1 : Int) ^ 14 := by
  simpa [fib_eq_natFib] using cassini_14

end Math

/-!
# Cassini 14
Category: Pure Mathematics
Target: Math.cassini_14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, valued in `ℤ`: `F 0 = 0`, `F 1 = 1`,
`F (n + 2) = F n + F (n + 1)`. -/
