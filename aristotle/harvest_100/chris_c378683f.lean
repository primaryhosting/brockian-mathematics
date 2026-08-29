import Mathlib
import RequestProject.Math

/-!
# Compatibility with Mathlib's Fibonacci numbers

`Math.fib` (defined without any Mathlib import, so that the target file
`RequestProject/Math.lean` can begin with its required header comment) agrees with
Mathlib's `Nat.fib`.  We restate Cassini's identity at `n = 15` in terms of `Nat.fib`,
and also derive it from Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n : Nat, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1), Nat.fib_add_two]

/-- Cassini's identity at `n = 15`, stated with Mathlib's `Nat.fib`. -/
theorem cassini_15_nat_fib :
    (Nat.fib 14 : ℤ) * (Nat.fib 16 : ℤ) - (Nat.fib 15 : ℤ) ^ 2 = (-1) ^ 15 := by
  simpa [fib_eq_nat_fib] using Math.cassini_15

/-- The same statement, obtained as an instance of Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/
theorem cassini_15_of_mathlib :
    (Nat.fib 14 : ℤ) * (Nat.fib 16 : ℤ) - (Nat.fib 15 : ℤ) ^ 2 = (-1) ^ 15 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq (15 : ℤ)
  rw [show ((15 : ℤ) + 1) = ((16 : ℕ) : ℤ) by norm_num,
      show ((15 : ℤ) - 1) = ((14 : ℕ) : ℤ) by norm_num,
      show ((15 : ℤ)) = ((15 : ℕ) : ℤ) by norm_num,
      Int.fib_natCast, Int.fib_natCast, Int.fib_natCast] at h
  rw [show ((15 : ℕ) : ℤ).natAbs = 15 by norm_num] at h
  linarith [h]

end Math

/-!
# Cassini 15
Category: Pure Mathematics
Target: Math.cassini_15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n + 2) = fib n + fib (n + 1)`.
This agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_nat_fib` in `RequestProject.MathFib`). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity at `n = 15`**: `F(14) * F(16) - F(15)^2 = (-1)^15`. -/
theorem cassini_15 :
    (fib 14 : Int) * (fib 16 : Int) - (fib 15 : Int) ^ 2 = (-1) ^ 15 := by
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

