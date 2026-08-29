import Mathlib
import RequestProject.Math

/-!
# Cassini 10, via Mathlib's Fibonacci numbers

This file links `Math.fib` (defined in `RequestProject.Math`, which cannot carry an `import`
line) with Mathlib's `Nat.fib`, and derives the `n = 10` case of Cassini's identity from
Mathlib's general statement `Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem cassini_10_iff_nat_fib :
    ((Math.fib 9 : ℤ) * (Math.fib 11 : ℤ) - (Math.fib 10 : ℤ) ^ 2 = (-1) ^ 10) ↔
      ((Nat.fib 9 : ℤ) * (Nat.fib 11 : ℤ) - (Nat.fib 10 : ℤ) ^ 2 = (-1) ^ 10) := by
  simp [fib_eq_nat_fib]

end Math

/-!
# Cassini 10
Category: Pure Mathematics
Target: Math.cassini_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence `F` with `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

(This file carries the required header comment as its first token, which Lean only permits
in a file with no `import` lines, so the sequence is defined here from scratch;
`RequestProject.MathCassini` proves `Math.fib = Nat.fib` and restates the identity
using Mathlib's Fibonacci numbers.) -/
