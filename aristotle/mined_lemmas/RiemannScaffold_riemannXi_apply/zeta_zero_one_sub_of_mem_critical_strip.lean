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


theorem zeta_zero_one_sub_of_mem_critical_strip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 := by
  have hr : (1 - s).re = 1 - s.re := by simp
  have hstrip0 : 0 < (1 - s).re := by rw [hr]; linarith
  have hstrip1 : (1 - s).re < 1 := by rw [hr]; linarith
  have hxi : RiemannScaffold.riemannXi s = 0 :=
    (riemannXi_eq_zero_iff_zeta_zero_of_mem_critical_strip h0 h1).mpr hz
  have hxi' : RiemannScaffold.riemannXi (1 - s) = 0 := by
    rw [riemannXi_functional_equation]; exact hxi
  exact (riemannXi_eq_zero_iff_zeta_zero_of_mem_critical_strip hstrip0 hstrip1).mp hxi'

/-! ### Conjugation symmetry of the Riemann zeta function -/

/-- On the half-plane of absolute convergence, `ζ` commutes with complex conjugation. -/
