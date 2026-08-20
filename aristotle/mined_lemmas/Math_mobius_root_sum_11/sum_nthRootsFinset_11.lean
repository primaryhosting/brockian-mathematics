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

theorem sum_nthRootsFinset_11 : ∑ x ∈ nthRootsFinset 11 (1 : ℂ), x = 0 := by
  rw [nthRootsFinset_11_eq_image, Finset.sum_image
    (fun a ha b hb hab =>
      isPrimitiveRoot_zeta11.pow_inj (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) hab)]
  exact isPrimitiveRoot_zeta11.geom_sum_eq_zero (by norm_num)

/-- Since `11` is prime, every 11-th root of unity other than `1` is primitive. -/
