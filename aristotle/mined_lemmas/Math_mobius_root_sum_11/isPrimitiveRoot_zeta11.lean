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

open Polynomial Finset

namespace Math

/-- A concrete primitive 11-th root of unity in `ℂ`. -/

theorem isPrimitiveRoot_zeta11 : IsPrimitiveRoot zeta11 11 :=
  Complex.isPrimitiveRoot_exp 11 (by norm_num)

/-- The 11-th roots of unity are exactly the powers `zeta11 ^ i` for `i < 11`. -/
