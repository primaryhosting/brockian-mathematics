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

set_option grind.warning false

namespace Chem

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

lemma geom_sum_19 {z : ℂ} (h1 : z ^ 19 = 1) (h2 : z ≠ 1) :
    ∑ i ∈ Finset.range 19, z ^ i = 0 := by
  rw [geom_sum_eq h2 19, h1, sub_self, zero_div]

