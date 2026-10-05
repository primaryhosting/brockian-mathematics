/-!
# Cassini 3
Category: Pure Mathematics
Target: Math.cassini_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, with `fib 0 = 0` and `fib 1 = 1`. -/

theorem cassini_3 :
    (fib 2 : Int) * (fib 4 : Int) - (fib 3 : Int) ^ 2 = (-1) ^ 3 := by
  decide

end Math

import Mathlib
import RequestProject.Cassini3

/-!
# Cassini 3, stated with Mathlib's `Nat.fib`

Supplementary file: identifies the local `Math.fib` with Mathlib's `Nat.fib`
and restates Cassini's identity at `n = 3` in those terms.
-/

namespace Math

/-- The local Fibonacci function agrees with Mathlib's `Nat.fib`. -/
