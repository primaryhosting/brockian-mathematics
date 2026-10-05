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
theorem fib_eq_nat_fib : ∀ n : ℕ, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 12`, stated with Mathlib's `Nat.fib`, obtained by
specializing Mathlib's `Int.fib_succ_mul_fib_pred_sub_fib_sq` to `n = 12`. -/
theorem cassini_12_nat_fib :
    (Nat.fib 11 : ℤ) * (Nat.fib 13 : ℤ) - (Nat.fib 12 : ℤ) ^ 2 = (-1) ^ 12 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 12
  simpa [Int.fib] using h

/-- The target theorem `Math.cassini_12` indeed states Cassini's identity for the
Mathlib Fibonacci numbers. -/
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
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 12`: `F(11) · F(13) − F(12)² = (−1)^12`.

Numerically: `89 * 233 - 144 ^ 2 = 20737 - 20736 = 1`. -/
theorem cassini_12 :
    (fib 11 : Int) * (fib 13 : Int) - (fib 12 : Int) ^ 2 = (-1) ^ 12 := by
  decide

end Math

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

