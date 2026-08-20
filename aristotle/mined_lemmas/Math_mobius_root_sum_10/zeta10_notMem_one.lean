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

namespace Math

/-- A fixed primitive 10-th root of unity in `ℂ`. -/

theorem zeta10_notMem_one : zeta10 ∉ ({zeta10 ^ 3, zeta10 ^ 7, zeta10 ^ 9} : Finset ℂ) := by
  have h13 : zeta10 ≠ zeta10 ^ 3 := by
    simpa using zeta10_pow_ne (i := 1) (j := 3) (by norm_num) (by norm_num) (by norm_num)
  have h17 : zeta10 ≠ zeta10 ^ 7 := by
    simpa using zeta10_pow_ne (i := 1) (j := 7) (by norm_num) (by norm_num) (by norm_num)
  have h19 : zeta10 ≠ zeta10 ^ 9 := by
    simpa using zeta10_pow_ne (i := 1) (j := 9) (by norm_num) (by norm_num) (by norm_num)
  simp [h13, h17, h19]

