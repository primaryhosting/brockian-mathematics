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

theorem zeta10_sum_eq_one : zeta10 + zeta10 ^ 3 + zeta10 ^ 7 + zeta10 ^ 9 = 1 := by
  have h5 : zeta10 ^ 5 = -1 := zeta10_pow_five
  have hne : zeta10 + 1 ≠ 0 := by
    intro h
    have hm : zeta10 = -1 := by linear_combination h
    have h2 : zeta10 ^ 2 = 1 := by rw [hm]; ring
    exact isPrimitiveRoot_zeta10.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) h2
  have key : zeta10 ^ 4 - zeta10 ^ 3 + zeta10 ^ 2 - zeta10 + 1 = 0 := by
    have hp : (zeta10 + 1) * (zeta10 ^ 4 - zeta10 ^ 3 + zeta10 ^ 2 - zeta10 + 1) = 0 := by
      linear_combination h5
    rcases mul_eq_zero.1 hp with h | h
    · exact absurd h hne
    · exact h
  have h7 : zeta10 ^ 7 = -zeta10 ^ 2 := by
    have h : zeta10 ^ 7 = zeta10 ^ 5 * zeta10 ^ 2 := by ring
    rw [h, h5]; ring
  have h9 : zeta10 ^ 9 = -zeta10 ^ 4 := by
    have h : zeta10 ^ 9 = zeta10 ^ 5 * zeta10 ^ 4 := by ring
    rw [h, h5]; ring
  rw [h7, h9]; linear_combination -key

