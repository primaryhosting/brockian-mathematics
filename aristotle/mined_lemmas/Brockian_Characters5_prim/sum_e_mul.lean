import Mathlib

/-!
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/

theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  have h : omega ^ 0 + omega ^ 1 + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
    have := sum_omega_pow
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one] at this
    linear_combination this
  have ha : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by revert a; decide
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · rw [sum_univ_zmod5, if_pos rfl]
    show omega ^ 0 + omega ^ 0 + omega ^ 0 + omega ^ 0 + omega ^ 0 = 5
    norm_num
  · rw [sum_univ_zmod5, if_neg (by decide : (1 : ZMod 5) ≠ 0)]
    show omega ^ 0 + omega ^ 1 + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0
    linear_combination h
  · rw [sum_univ_zmod5, if_neg (by decide : (2 : ZMod 5) ≠ 0)]
    show omega ^ 0 + omega ^ 2 + omega ^ 4 + omega ^ 1 + omega ^ 3 = 0
    linear_combination h
  · rw [sum_univ_zmod5, if_neg (by decide : (3 : ZMod 5) ≠ 0)]
    show omega ^ 0 + omega ^ 3 + omega ^ 1 + omega ^ 4 + omega ^ 2 = 0
    linear_combination h
  · rw [sum_univ_zmod5, if_neg (by decide : (4 : ZMod 5) ≠ 0)]
    show omega ^ 0 + omega ^ 4 + omega ^ 3 + omega ^ 2 + omega ^ 1 = 0
    linear_combination h

end Brockian.Characters5

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

