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

theorem conj_omega7_pow (m : ℕ) :
    (starRingEnd ℂ) (omega7 ^ m) = (omega7 ^ m)⁻¹ := by
  rw [Complex.inv_eq_conj]
  rw [norm_pow, norm_omega7, one_pow]

/-- Key orthogonality: the geometric sum of `z ^ l` over `l < 128`, where `z` is a
power of `omega7`, is `128` if `z = 1` and `0` otherwise. -/
