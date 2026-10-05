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

/-
The moduli `1 + (i+1)q` used to code finite sequences, and the Chinese remainder theorem
for them.
-/
import RequestProject.H10.Arith

open Dioph Finset

namespace H10

/-- The `i`-th modulus of the Chinese remainder coding with parameter `q`. -/

theorem diophFn_factorial {f : (α → ℕ) → ℕ} (df : DiophFn f) :
    DiophFn fun v => (f v).factorial := by
  have dr : DiophFn fun v => (f v + 1) ^ (2 * f v + 4) :=
    diophFn_pow (diophFn_add df (diophFn_const 1))
      (diophFn_add (diophFn_mul (diophFn_const 2) df) (diophFn_const 4))
  have key : DiophFn fun v =>
      ((f v + 1) ^ (2 * f v + 4)) ^ f v / ((f v + 1) ^ (2 * f v + 4)).choose (f v) :=
    diophFn_div (diophFn_pow dr df) (diophFn_choose dr df)
  exact DiophFn.congr key fun v => (factorial_eq_div (f v) _ (factorial_bound (f v))).symm

/-! ### Products of arithmetic progressions -/

/-- The product `(a+b)(a+2b)⋯(a+mb)`. -/
