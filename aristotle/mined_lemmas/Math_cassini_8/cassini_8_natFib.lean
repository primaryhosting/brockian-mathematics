import Mathlib
import RequestProject.Main

/-!
# Bridge to Mathlib's `Nat.fib`

`Math.fib` (defined in `RequestProject.Main` without imports, as required by the
file header there) agrees with Mathlib's `Nat.fib`, so `Math.cassini_8` is a
statement about the usual Fibonacci numbers.
-/

namespace Math


theorem cassini_8_natFib :
    (Nat.fib 7 : ℤ) * (Nat.fib 9 : ℤ) - (Nat.fib 8 : ℤ) ^ 2 = (-1) ^ 8 := by
  simpa [fib_eq_natFib] using cassini_8

end Math

/-!
# Cassini 8
Category: Pure Mathematics
Target: Math.cassini_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, with `fib 0 = 0` and `fib 1 = 1`.
This agrees with `Nat.fib` from Mathlib; it is defined here because the
required header comment must be the very first item in the file, which
precludes an `import` command. -/
