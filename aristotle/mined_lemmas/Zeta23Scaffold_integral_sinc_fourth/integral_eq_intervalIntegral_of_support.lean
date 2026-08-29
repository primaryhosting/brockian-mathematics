import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Scaffold

open MeasureTheory Real FourierTransform Complex intervalIntegral

/-- The tent (triangle) function `max 0 (1 - |x|)`, viewed as a complex-valued function. -/

lemma integral_eq_intervalIntegral_of_support {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (h : ∀ x : ℝ, 1 ≤ |x| → f x = 0) :
    ∫ x : ℝ, f x = ∫ x in (-1 : ℝ)..1, f x := by
  rw [intervalIntegral.integral_of_le (by norm_num),
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioc (-1 : ℝ) 1)]
  intro x hx
  apply h
  simp only [Set.mem_Ioc, not_and_or, not_le, not_lt] at hx
  rcases hx with hx | hx
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

/-- `∫_ℝ (max 0 (1 - |x|))^n = 2/(n+1)` for `n ≥ 1`. -/
