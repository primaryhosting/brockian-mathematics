/-!
# Cassini 15
Category: Pure Mathematics
Target: Math.cassini_15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
This agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_nat_fib` in `Cassini15Mathlib.lean`). -/

theorem cassini_15 :
    (fib 14 : Int) * (fib 16 : Int) - (fib 15 : Int) ^ 2 = (-1) ^ 15 := by
  decide

end Math

import Mathlib
import RequestProject.Cassini15

/-!
# Cassini 15, stated with Mathlib's `Nat.fib`

The target theorem `Math.cassini_15` lives in `Cassini15.lean`, whose required header comment
must be the very first thing in that file; since a module docstring cannot precede `import`
statements, that file is self-contained and uses its own `Math.fib`.  Here we check that
`Math.fib` really is Mathlib's `Nat.fib`, and restate Cassini's identity accordingly.
-/

namespace Math

