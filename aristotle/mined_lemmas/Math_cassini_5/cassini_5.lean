/-!
# Cassini 5
Category: Pure Mathematics
Target: Math.cassini_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, with `fib 0 = 0` and `fib 1 = 1`. -/

theorem cassini_5 :
    (fib 4 : Int) * (fib 6 : Int) - (fib 5 : Int) ^ 2 = (-1 : Int) ^ 5 := by
  decide

end Math

import Mathlib
import RequestProject.Cassini5

/-!
# Cassini 5 (Mathlib version)

The header of `RequestProject/Cassini5.lean` is required to be the very first thing in that
file, which prevents an `import` line there; so the statement in terms of Mathlib's `Nat.fib`
is recorded here, together with the agreement `Math.fib = Nat.fib`.
-/

namespace Math

