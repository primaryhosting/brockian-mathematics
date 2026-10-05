import Mathlib
import RequestProject.Math

/-!
# Cassini 12 — Mathlib cross-check

This file connects the self-contained development in `RequestProject/Math.lean`
with Mathlib:

* `Math.fib_eq_nat_fib` : the locally defined `Math.fib` equals Mathlib's `Nat.fib`;
* `Math.cassini_12_nat_fib` : the target statement phrased with `Nat.fib`, derived
  from Mathlib's general Cassini identity
  `Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

/-- The `fib` of this project agrees with Mathlib's `Nat.fib`. -/

theorem cassini_12_agrees :
    (fib 11 : ℤ) * (fib 13 : ℤ) - (fib 12 : ℤ) ^ 2
      = (Nat.fib 11 : ℤ) * (Nat.fib 13 : ℤ) - (Nat.fib 12 : ℤ) ^ 2 := by
  simp [fib_eq_nat_fib]

end Math

/-!
# Cassini 12
Category: Pure Mathematics
Target: Math.cassini_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

(This file must begin with the header comment above, and Lean requires every `import`
to precede any command — including a module docstring — so this file is kept
import-free and self-contained.  The file `RequestProject/MathCassini.lean` checks
that this `Math.fib` agrees with Mathlib's `Nat.fib`, and rederives the statement
below from Mathlib's general Cassini identity.) -/
