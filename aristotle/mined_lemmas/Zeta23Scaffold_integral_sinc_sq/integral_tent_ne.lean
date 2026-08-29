import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Zeta23Scaffold

open MeasureTheory Real Complex
open scoped FourierTransform

/-! ### The triangular (tent) function and its Fourier transform -/

/-- The tent function `t ↦ max (1 - |t|) 0`, real valued. -/

lemma integral_tent_ne (c : ℝ) (hc : c ≠ 0) :
    ∫ v in (-1 : ℝ)..1, ee c v * tent v = (((2 - 2 * Real.cos c) / c ^ 2 : ℝ) : ℂ) := by
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun v => ee c v * tent v) volume x y :=
    fun x y => Continuous.intervalIntegrable ((continuous_ee c).mul continuous_tent) x y
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ)) (hint (-1) 0) (hint 0 1)]
  have e1 : ∫ v in (-1 : ℝ)..0, ee c v * tent v
      = ∫ v in (-1 : ℝ)..0, ee c v * ((1 + 1 * v : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hv
    have h : |v| = -v := abs_of_nonpos hv.2
    simp only [tent, tentR, h]
    norm_num
    left
    rw [max_eq_left (by linarith [hv.1])]
    push_cast
    ring
  have e2 : ∫ v in (0 : ℝ)..1, ee c v * tent v
      = ∫ v in (0 : ℝ)..1, ee c v * ((1 + (-1) * v : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    have h : |v| = v := abs_of_nonneg hv.1
    simp only [tent, tentR, h]
    norm_num
    left
    rw [max_eq_left (by linarith [hv.2])]
    push_cast
    ring
  rw [e1, e2, integral_piece c hc, integral_piece c hc]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hee0 : ee c 0 = 1 := by simp [ee]
  simp only [antid, hee0]
  have hs := sum_ee c
  push_cast
  field_simp
  linear_combination (-I) * hs

/-- The tent integral at frequency zero. -/
