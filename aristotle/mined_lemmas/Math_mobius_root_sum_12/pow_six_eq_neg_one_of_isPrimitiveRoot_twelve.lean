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
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/



namespace Math

open Finset

/-- A primitive 12-th root of unity satisfies `z ^ 6 = -1`. -/

lemma pow_six_eq_neg_one_of_isPrimitiveRoot_twelve {z : ℂ} (h : IsPrimitiveRoot z 12) :
    z ^ 6 = -1 := by
  have h12 : z ^ 12 = 1 := h.pow_eq_one
  have hfac : (z ^ 6 - 1) * (z ^ 6 + 1) = 0 := by
    have hexp : (z ^ 6 - 1) * (z ^ 6 + 1) = z ^ 12 - 1 := by ring
    rw [hexp, h12, sub_self]
  have hne : z ^ 6 ≠ 1 := h.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  rcases mul_eq_zero.1 hfac with h1 | h2
  · exact absurd (sub_eq_zero.1 h1) hne
  · linear_combination h2

/-- The negative of a primitive 12-th root of unity is again one:
`-z = z ^ 6 * z = z ^ 7` and `7` is coprime to `12`. -/
