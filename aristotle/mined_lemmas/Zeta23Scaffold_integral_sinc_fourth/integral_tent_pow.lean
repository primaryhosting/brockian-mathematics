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

lemma integral_tent_pow (n : ℕ) (hn : n ≠ 0) :
    ∫ x : ℝ, (max 0 (1 - |x|)) ^ n = 2 / (n + 1) := by
  have key : ∫ x : ℝ, (max 0 (1 - |x|)) ^ n = ∫ x in (-1 : ℝ)..1, (max 0 (1 - |x|)) ^ n := by
    apply integral_eq_intervalIntegral_of_support
    intro x hx
    rw [max_eq_left (by linarith), zero_pow hn]
  rw [key, ← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ)) (a := -1) (c := 1)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have h1 : ∫ x in (-1 : ℝ)..0, (max 0 (1 - |x|)) ^ n = ∫ x in (-1 : ℝ)..0, (1 + x) ^ n := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0), Set.mem_Icc] at hx
    dsimp only
    rw [abs_of_nonpos hx.2, max_eq_right (by linarith)]
    ring_nf
  have h2 : ∫ x in (0 : ℝ)..1, (max 0 (1 - |x|)) ^ n = ∫ x in (0 : ℝ)..1, (1 - x) ^ n := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.mem_Icc] at hx
    dsimp only
    rw [abs_of_nonneg hx.1, max_eq_right (by linarith)]
  rw [h1, h2,
    show (fun x : ℝ => (1 + x) ^ n) = (fun x : ℝ => (fun y : ℝ => y ^ n) (x + 1)) by
      ext x; ring_nf,
    show (fun x : ℝ => (1 - x) ^ n) = (fun x : ℝ => (fun y : ℝ => y ^ n) (1 - x)) by
      ext x; ring_nf,
    intervalIntegral.integral_comp_add_right (fun y : ℝ => y ^ n) 1,
    intervalIntegral.integral_comp_sub_left (fun y : ℝ => y ^ n) 1]
  norm_num [integral_pow]
  ring

/-- The Fourier transform of the tent function, written as an interval integral. -/
