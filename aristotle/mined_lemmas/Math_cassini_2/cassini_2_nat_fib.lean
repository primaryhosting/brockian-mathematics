import Mathlib
import RequestProject.Cassini2

/-!
# Cassini 2, in terms of Mathlib's `Nat.fib`
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem cassini_2_nat_fib :
    (Nat.fib 1 : ℤ) * (Nat.fib 3 : ℤ) - (Nat.fib 2 : ℤ) ^ 2 = (-1 : ℤ) ^ 2 := by
  simpa [fib_eq_nat_fib] using cassini_2

end Math

/-!
# Cassini 2
Category: Pure Mathematics
Target: Math.cassini_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean does not permit `import` commands after a module docstring (`/-! ... -/`),
so this file, which must begin with the docstring above, is self-contained and uses
only Lean core.  The companion file `RequestProject/Cassini2Mathlib.lean` imports
Mathlib and identifies `Math.fib` with `Nat.fib`, restating the result in terms of
Mathlib's Fibonacci function.
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/
