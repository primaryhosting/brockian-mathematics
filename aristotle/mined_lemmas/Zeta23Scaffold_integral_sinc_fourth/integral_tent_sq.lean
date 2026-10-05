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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Scaffold

open MeasureTheory Real FourierTransform intervalIntegral

/-! ## The tent function and its Fourier transform -/

/-- The tent (triangle) function, supported on `[-1, 1]`. -/

lemma integral_tent_sq : ∫ x : ℝ, tent x ^ 2 = 2 / 3 := by
  have hc : Continuous (fun x : ℝ => tent x ^ 2) := continuous_tent.pow 2
  have h1 : ∫ x in Set.Ioc (-1:ℝ) 1, tent x ^ 2 = ∫ x : ℝ, tent x ^ 2 := by
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [tent_eq_zero (one_le_abs_of_notMem_Ioc hx)]
  rw [← h1, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  have hsplit : ∫ x in (-1:ℝ)..1, tent x ^ 2 = ∫ x in (0:ℝ)..1, (tent (-x) ^ 2 + tent x ^ 2) := by
    have h2 : IntervalIntegrable (fun x : ℝ => tent (-x) ^ 2) volume 0 1 :=
      (hc.comp continuous_neg).intervalIntegrable _ _
    rw [intervalIntegral.integral_add h2 (hc.intervalIntegrable _ _),
      intervalIntegral.integral_comp_neg (fun x : ℝ => tent x ^ 2),
      ← intervalIntegral.integral_add_adjacent_intervals (a := (-1:ℝ)) (b := 0) (c := 1)
        (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    norm_num
  rw [hsplit]
  have hcongr : ∀ x ∈ Set.uIcc (0:ℝ) 1, tent (-x) ^ 2 + tent x ^ 2 = 2 * (1 - x) ^ 2 := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    obtain ⟨h0, h1⟩ := hx
    have habs : |x| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
    rw [tent_of_mem habs, tent_of_mem (by rwa [abs_neg]), abs_neg, abs_of_nonneg h0]
    ring
  rw [intervalIntegral.integral_congr hcongr]
  simp only [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ 2) 1]
  norm_num

/-! ## Assembling the pieces -/

