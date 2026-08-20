/-!
# Cassini 4
Category: Pure Mathematics
Target: Math.cassini_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
This agrees with Mathlib's `Nat.fib`; see `Math.fib_eq_nat_fib` in `Cassini4Mathlib.lean`.
(It is defined here rather than imported because the required module header comment must be
the very first thing in this file, which precludes an `import` statement.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity at `n = 4`**: `F(3) * F(5) - F(4)^2 = (-1)^4`, computed in `ℤ`. -/
theorem cassini_4 :
    (fib 3 : Int) * (fib 5 : Int) - (fib 4 : Int) ^ 2 = (-1 : Int) ^ 4 := by
  decide

end Math

import Mathlib
import RequestProject.Cassini4

/-!
# Cassini 4 — Mathlib version

Category: Pure Mathematics
Target: Math.cassini_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This companion file connects `Math.fib` to Mathlib's `Nat.fib`, restates Cassini's identity
at `n = 4` for `Nat.fib`, and derives it from Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

/-- The locally defined `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n : ℕ, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1), Nat.add_comm]

/-- Cassini's identity at `n = 4`, stated with Mathlib's `Nat.fib`. -/
theorem cassini_4_nat_fib :
    (Nat.fib 3 : ℤ) * (Nat.fib 5 : ℤ) - (Nat.fib 4 : ℤ) ^ 2 = (-1 : ℤ) ^ 4 := by
  simpa [fib_eq_nat_fib] using Math.cassini_4

/-- Cassini's identity at `n = 4` obtained directly from Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/
theorem cassini_4_from_mathlib :
    Int.fib (4 + 1) * Int.fib (4 - 1) - Int.fib 4 ^ 2 = (-1 : ℤ) ^ (4 : ℤ).natAbs :=
  Int.fib_succ_mul_fib_pred_sub_fib_sq 4

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

