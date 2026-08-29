import Mathlib
import RequestProject.Cassini4

/-!
# Cassini 4, phrased with Mathlib's `Nat.fib`
-/

namespace Math

/-- The locally defined Fibonacci sequence agrees with Mathlib's `Nat.fib`. -/

theorem cassini_4_fib :
    (Nat.fib 3 : ℤ) * (Nat.fib 5 : ℤ) - (Nat.fib 4 : ℤ) ^ 2 = (-1 : ℤ) ^ 4 := by
  simpa [F_eq_fib] using cassini_4

end Math

/-!
# Cassini 4
Category: Pure Mathematics
Target: Math.cassini_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

(This file is kept import-free so that the required header comment can be the very first
thing in the file; Lean does not allow a module doc comment to precede an `import`.
The Mathlib version of the statement, phrased with `Nat.fib`, is in `Cassini4Fib.lean`.) -/
