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


theorem zeta_zero_quartet_of_mem_critical_strip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0) :
    riemannZeta s = 0 ∧ riemannZeta (1 - s) = 0 ∧
      riemannZeta (starRingEnd ℂ s) = 0 ∧
      riemannZeta (1 - starRingEnd ℂ s) = 0 := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at h1
  have hconj : riemannZeta (starRingEnd ℂ s) = 0 := by
    rw [riemannZeta_conj hs1, hz, map_zero]
  have hcre : ((starRingEnd ℂ) s).re = s.re := Complex.conj_re s
  refine ⟨hz, zeta_zero_one_sub_of_mem_critical_strip h0 h1 hz, hconj, ?_⟩
  refine zeta_zero_one_sub_of_mem_critical_strip (by rw [hcre]; exact h0)
    (by rw [hcre]; exact h1) hconj

