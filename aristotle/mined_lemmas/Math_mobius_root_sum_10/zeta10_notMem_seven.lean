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

theorem zeta10_notMem_seven : zeta10 ^ 7 ∉ ({zeta10 ^ 9} : Finset ℂ) := by
  have h79 : zeta10 ^ 7 ≠ zeta10 ^ 9 :=
    zeta10_pow_ne (by norm_num) (by norm_num) (by norm_num)
  simp [h79]

/-- The finset of primitive 10-th roots of unity in `ℂ`, explicitly. -/
