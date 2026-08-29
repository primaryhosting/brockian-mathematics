import Mathlib
import RequestProject.Cassini14

/-!
# Cassini 14 (Mathlib restatement)

This file identifies the self-contained Fibonacci sequence `Math.F` of
`RequestProject/Cassini14.lean` with Mathlib's `Nat.fib`, and restates Cassini's
identity at `n = 14` in terms of `Nat.fib`.
-/

namespace Math


theorem cassini_14_fib :
    (Nat.fib 13 : ℤ) * (Nat.fib 15 : ℤ) - (Nat.fib 14 : ℤ) ^ 2 = (-1) ^ 14 := by
  simpa [F_eq_fib] using cassini_14

end Math

/-!
# Cassini 14
Category: Pure Mathematics
Target: Math.cassini_14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 does not permit any comment (including this header) to precede an
-- `import` line, so this file is deliberately import-free and self-contained.
-- The companion file `RequestProject/Cassini14Mathlib.lean` connects the Fibonacci
-- numbers defined here with Mathlib's `Nat.fib` and restates the result.

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`. -/
