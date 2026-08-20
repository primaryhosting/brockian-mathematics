/-!
# Cassini 4
Category: Pure Mathematics
Target: Math.cassini_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean requires all `import` commands to precede any other command, including
module doc comments.  Since the requested header must be the very first thing in
this file, the file is kept self-contained (no imports beyond the core prelude)
and the Fibonacci sequence is defined directly below with the standard recursion,
matching `Nat.fib` (`F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`).
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`. -/

theorem cassini_4 : (fib 3 : Int) * (fib 5 : Int) - (fib 4 : Int) ^ 2 = (-1) ^ 4 := by
  decide

end Math

import Mathlib
import RequestProject.Cassini4

/-!
# Cassini 4 (Mathlib companion)

This file connects the self-contained `Math.fib` of `RequestProject/Cassini4.lean`
with Mathlib's `Nat.fib`, and restates Cassini's identity at `n = 4` for `Nat.fib`.
-/

namespace Math

/-- The locally defined Fibonacci sequence agrees with Mathlib's `Nat.fib`. -/
