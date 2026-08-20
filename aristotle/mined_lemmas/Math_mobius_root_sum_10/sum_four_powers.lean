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

open Complex ArithmeticFunction

/-- The Möbius function at `10` equals `1`. -/

lemma sum_four_powers {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) :
    ζ ^ 1 + ζ ^ 3 + ζ ^ 7 + ζ ^ 9 = 1 := by
  have h5 : ζ ^ 5 = -1 := pow_five_eq_neg_one h
  have hne : ζ + 1 ≠ 0 := by
    intro hz
    have hz' : ζ = -1 := by linear_combination hz
    have := h.pow_ne_one_of_pos_of_lt (l := 2) (by norm_num) (by norm_num)
    apply this
    rw [hz']; norm_num
  have key : (ζ + 1) * (ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1) = 0 := by
    linear_combination h5
  have h4 : ζ ^ 4 - ζ ^ 3 + ζ ^ 2 - ζ + 1 = 0 :=
    (mul_eq_zero.1 key).resolve_left hne
  have h7 : ζ ^ 7 = -ζ ^ 2 := by
    have : ζ ^ 7 = ζ ^ 5 * ζ ^ 2 := by ring
    rw [this, h5]; ring
  have h9 : ζ ^ 9 = -ζ ^ 4 := by
    have : ζ ^ 9 = ζ ^ 5 * ζ ^ 4 := by ring
    rw [this, h5]; ring
  rw [h7, h9]
  linear_combination -h4

/-- The set of primitive `10`-th roots of unity in `ℂ`, described explicitly in terms of
one of them. -/
