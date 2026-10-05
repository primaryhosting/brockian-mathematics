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

namespace RiemannScaffold


theorem riemannZeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) s)) = riemannZeta s := by
  have hs' : 1 < ((starRingEnd ℂ) s).re := by simpa using hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs', zeta_eq_tsum_one_div_nat_add_one_cpow hs,
    Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  have harg : ((n : ℂ) + 1).arg ≠ Real.pi := by
    have : ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.arg_ofReal_of_nonneg (by positivity)]
    exact fun h => Real.pi_ne_zero h.symm
  have hconj : (starRingEnd ℂ) ((n : ℂ) + 1) = (n : ℂ) + 1 := by
    simp
  have := Complex.conj_cpow ((n : ℂ) + 1) s harg
  rw [hconj] at this
  rw [map_div₀]
  simp only [map_one]
  rw [← this]

/-- `ζ` commutes with complex conjugation away from the pole. -/
