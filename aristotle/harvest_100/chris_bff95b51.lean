/-
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
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

namespace Frontier

open MeasureTheory intervalIntegral Set

/-- Auxiliary: for a `C¹` function with compact support on `ℝ`, `|f'|` is integrable. -/
theorem integrable_abs_deriv_of_contDiff_of_hasCompactSupport
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hsupp : HasCompactSupport f) :
    Integrable (fun t => |deriv f t|) volume := by
  have hcont : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hcs : HasCompactSupport (deriv f) := hsupp.deriv
  have : Integrable (deriv f) volume := hcont.integrable_of_hasCompactSupport hcs
  exact this.abs

/-- The one-dimensional endpoint case of the Gagliardo–Nirenberg interpolation
inequality: for a continuously differentiable function `f : ℝ → ℝ` with compact
support, the sup-norm of `f` is bounded by half the `L¹` norm of its derivative,
`‖f‖_∞ ≤ (1/2) ‖f'‖_1`. -/
theorem nirenberg_gagliardo {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : HasCompactSupport f) (x : ℝ) :
    |f x| ≤ (1 / 2) * ∫ t, |deriv f t| := by
  classical
  have hderiv : ∀ t : ℝ, HasDerivAt f (deriv f t) t := fun t =>
    (hf.differentiable (by norm_num) t).hasDerivAt
  have hcont : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hint : Integrable (fun t => |deriv f t|) volume :=
    integrable_abs_deriv_of_contDiff_of_hasCompactSupport hf hsupp
  -- choose an interval `[a, b]` containing `x` and the support of `f`
  obtain ⟨R, hR⟩ : ∃ R : ℝ, tsupport f ⊆ Set.Icc (-R) R := by
    obtain ⟨R, hR⟩ := (hsupp.isCompact.isBounded).subset_closedBall 0
    exact ⟨R, by simpa [Real.closedBall_eq_Icc] using hR⟩
  set a : ℝ := min (x - 1) (-R - 1) with ha
  set b : ℝ := max (x + 1) (R + 1) with hb
  have hax : a ≤ x := le_trans (min_le_left _ _) (by linarith)
  have hxb : x ≤ b := le_trans (by linarith : x ≤ x + 1) (le_max_left _ _)
  have hab : a ≤ b := hax.trans hxb
  have hfa : f a = 0 := by
    have ha' : a ∉ tsupport f := fun h => by
      have h1 : a ≤ -R - 1 := min_le_right _ _
      linarith [(hR h).1]
    exact image_eq_zero_of_notMem_tsupport ha'
  have hfb : f b = 0 := by
    have hb' : b ∉ tsupport f := fun h => by
      have hb1 : R + 1 ≤ b := le_max_right _ _
      linarith [(hR h).2]
    exact image_eq_zero_of_notMem_tsupport hb'
  -- integrability of `deriv f` on intervals
  have hii : ∀ u v : ℝ, IntervalIntegrable (deriv f) volume u v := fun u v =>
    hcont.intervalIntegrable u v
  have hiia : ∀ u v : ℝ, IntervalIntegrable (fun t => |deriv f t|) volume u v := fun u v =>
    (hcont.abs).intervalIntegrable u v
  have key1 : ∫ t in a..x, deriv f t = f x := by
    rw [integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) (hii a x), hfa, sub_zero]
  have key2 : ∫ t in x..b, deriv f t = -f x := by
    rw [integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) (hii x b), hfb, zero_sub]
  have b1 : |f x| ≤ ∫ t in a..x, |deriv f t| := by
    rw [← key1]
    exact abs_integral_le_integral_abs hax
  have b2 : |f x| ≤ ∫ t in x..b, |deriv f t| := by
    have : |(-f x : ℝ)| ≤ ∫ t in x..b, |deriv f t| := by
      rw [← key2]
      exact abs_integral_le_integral_abs hxb
    simpa using this
  have hsum : (∫ t in a..x, |deriv f t|) + (∫ t in x..b, |deriv f t|)
      = ∫ t in a..b, |deriv f t| :=
    integral_add_adjacent_intervals (hiia a x) (hiia x b)
  have hle : (∫ t in a..b, |deriv f t|) ≤ ∫ t, |deriv f t| := by
    rw [integral_of_le hab]
    exact setIntegral_le_integral hint (Filter.Eventually.of_forall fun t => abs_nonneg _)
  linarith

end Frontier

#print axioms Frontier.nirenberg_gagliardo

