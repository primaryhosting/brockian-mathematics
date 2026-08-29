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

lemma fourier_tent_eq_intervalIntegral (w : ℝ) :
    𝓕 tent w = ∫ v in (-1 : ℝ)..1, ee (2 * π * w) v * tent v := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · apply MeasureTheory.integral_congr_ae
    filter_upwards with v
    rw [smul_eq_mul, ee, show (2 * π * w * v : ℝ) = 2 * π * v * w from by ring]
    norm_num
  · intro v hv
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hv
    have : 1 ≤ |v| := by
      rcases hv with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    simp [tent, tentR_eq_zero this]

/-- The Fourier transform of the tent function is `sinc (π w) ^ 2`. -/
