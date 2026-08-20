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

/-- The primitive `128`-th root of unity `exp (2 π i / 128)` used by the 7-qubit QFT. -/

theorem geom_sum_omega7 (d : ℤ) :
    ∑ l ∈ Finset.range 128, (omega7 ^ d) ^ l = if (128 : ℤ) ∣ d then 128 else 0 := by
  by_cases h : (128 : ℤ) ∣ d
  · have hz : omega7 ^ d = 1 := (omega7_isPrimitiveRoot.zpow_eq_one_iff_dvd d).2 h
    simp [hz, h]
  · have hz : omega7 ^ d ≠ 1 := fun hz =>
      h ((omega7_isPrimitiveRoot.zpow_eq_one_iff_dvd d).1 hz)
    rw [geom_sum_eq hz, if_neg h]
    have h128 : (omega7 ^ d) ^ (128 : ℕ) = 1 := by
      rw [← zpow_natCast (omega7 ^ d) 128, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, omega7_pow_128, one_zpow]
    rw [h128, sub_self, zero_div]

/-- The 7-qubit QFT matrix is unitary. -/
