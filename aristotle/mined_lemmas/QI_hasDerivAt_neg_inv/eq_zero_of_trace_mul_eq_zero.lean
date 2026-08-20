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

import Mathlib

/-!
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


theorem eq_zero_of_trace_mul_eq_zero (hω : ω.PosDef) {F : Mat n} (hF : F.PosSemidef)
    (h : (ω * F).trace.re = 0) : F = 0 := by
  have hcj : (cj hω F).PosSemidef := cj_posSemidef hω hF
  rw [trace_mul_re_eq_sum_eig hω] at h
  have hterm : ∀ i ∈ Finset.univ, eigV hω i * ((cj hω F) i i).re = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      mul_nonneg (eigV_pos hω i).le (diag_re_nonneg hcj i))).mp h
  have hzero : ∀ i, (cj hω F) i i = 0 := by
    intro i
    have hre : ((cj hω F) i i).re = 0 := by
      have := hterm i (Finset.mem_univ i)
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd h1 (ne_of_gt (eigV_pos hω i))
      · exact h1
    have him : ((cj hω F) i i).im = 0 := by
      have h0 : (0 : ℂ) ≤ (cj hω F) i i := hcj.diag_nonneg
      simpa using (Complex.le_def.mp h0).2.symm
    exact Complex.ext hre him
  refine hF.trace_eq_zero_iff.mp ?_
  rw [← trace_cj hω F]
  simp [Matrix.trace, Matrix.diag, hzero]

/-- A finite sum of positive semidefinite matrices is positive semidefinite. -/
