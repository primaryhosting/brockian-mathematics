/-!
# Cassini 9
Category: Pure Mathematics
Target: Math.cassini_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n + 2) = F n + F (n + 1)`.
    This agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_natFib`). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity at `n = 9`**: `F 8 * F 10 - F 9 ^ 2 = (-1) ^ 9`. -/
theorem cassini_9 : (fib 8 : Int) * (fib 10 : Int) - (fib 9 : Int) ^ 2 = (-1) ^ 9 := by
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

import Mathlib
import RequestProject.Cassini9

/-!
# Cassini 9, via Mathlib's Fibonacci API

This file connects `Math.fib` with Mathlib's `Nat.fib` and rederives the instance `n = 9`
of Cassini's identity from Mathlib's general result
`Int.fib_succ_mul_fib_pred_sub_fib_sq` (Cassini's identity:
`fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1) ^ |n|`).
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_natFib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    rw [fib, Nat.fib_add_two, fib_eq_natFib n, fib_eq_natFib (n + 1)]

/-- Cassini's identity at `n = 9`, stated with Mathlib's `Nat.fib`, obtained from
Mathlib's general Cassini identity `Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/
theorem cassini_9_natFib :
    (Nat.fib 8 : ℤ) * (Nat.fib 10 : ℤ) - (Nat.fib 9 : ℤ) ^ 2 = (-1) ^ 9 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 9
  rw [show (9 : ℤ) + 1 = ((10 : ℕ) : ℤ) by norm_num,
    show (9 : ℤ) - 1 = ((8 : ℕ) : ℤ) by norm_num,
    show (9 : ℤ) = ((9 : ℕ) : ℤ) by norm_num] at h
  rw [Int.fib_natCast, Int.fib_natCast, Int.fib_natCast] at h
  norm_num at h ⊢

end Math

