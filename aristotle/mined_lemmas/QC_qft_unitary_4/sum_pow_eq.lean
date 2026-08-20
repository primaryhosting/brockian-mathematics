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

namespace QC

/-- The primitive `16`-th root of unity `exp(2πi/16)` used for the 4-qubit QFT. -/

lemma sum_pow_eq (z : ℂ) (hz : z ^ (16 : ℕ) = 1) :
    ∑ i ∈ Finset.range 16, z ^ i = if z = 1 then (16 : ℂ) else 0 := by
  by_cases h : z = 1
  · simp [h]
  · rw [if_neg h, geom_sum_eq h, hz]
    simp

