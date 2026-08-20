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

lemma pow_five_eq_neg_one {ζ : ℂ} (h : IsPrimitiveRoot ζ 10) : ζ ^ 5 = -1 := by
  have h10 : (ζ ^ 5) ^ 2 = 1 := by
    rw [← pow_mul]; exact h.pow_eq_one
  have hne : ζ ^ 5 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  rcases mul_eq_zero.1 (show (ζ ^ 5 - 1) * (ζ ^ 5 + 1) = 0 by linear_combination h10) with h1 | h1
  · exact absurd (by linear_combination h1) hne
  · linear_combination h1

/-- The four primitive `10`-th roots of unity sum to `1`. -/
