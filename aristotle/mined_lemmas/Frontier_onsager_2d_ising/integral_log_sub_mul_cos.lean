/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

namespace Frontier

/-! ## The 2D Ising model on a finite torus -/

/-- The real value `±1` of a spin encoded as a `Bool`. -/

theorem integral_log_sub_mul_cos (a b : ℝ) (hb : |b| < a) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log (a - b * Real.cos θ)
      = 2 * Real.pi * Real.log ((a + Real.sqrt (a ^ 2 - b ^ 2)) / 2) := by
  have ha : 0 < a := lt_of_le_of_lt (abs_nonneg b) hb
  rcases eq_or_ne b 0 with hb0 | hb0
  · subst hb0
    rw [show a ^ 2 - (0 : ℝ) ^ 2 = a ^ 2 by ring, Real.sqrt_sq ha.le]
    simp only [zero_mul, sub_zero]
    rw [intervalIntegral.integral_const, show (a + a) / 2 = a by ring]
    simp
  · have hb2 : 0 < b ^ 2 := by positivity
    have hD : 0 < a ^ 2 - b ^ 2 := by nlinarith [sq_abs b, abs_nonneg b]
    set s := Real.sqrt (a ^ 2 - b ^ 2) with hs_def
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = a ^ 2 - b ^ 2 := Real.sq_sqrt hD.le
    have hsa : s < a := by
      have h := Real.sqrt_lt_sqrt hD.le (show a ^ 2 - b ^ 2 < a ^ 2 by nlinarith)
      rwa [Real.sqrt_sq ha.le] at h
    set r : ℝ := (a + s) / b with hr_def
    set r' : ℝ := (a - s) / b with hr'_def
    have hrr' : r * r' = 1 := by
      rw [hr_def, hr'_def]; field_simp; linear_combination -hs2
    have hsum : r + r' = 2 * a / b := by
      rw [hr_def, hr'_def]; field_simp; ring
    have hbabs : 0 < |b| := abs_pos.mpr hb0
    have habs_r : |r| = (a + s) / |b| := by
      rw [hr_def, abs_div, abs_of_pos (by linarith : (0:ℝ) < a + s)]
    have hr_gt : 1 < |r| := by
      rw [habs_r, lt_div_iff₀ hbabs]
      linarith [hb]
    have habs_r'_le : |r'| ≤ 1 := by
      have h1 : |r| * |r'| = 1 := by rw [← abs_mul, hrr']; simp
      nlinarith [abs_nonneg r']
    have hnormr : ‖(r : ℂ)‖ = |r| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have hnormr' : ‖(r' : ℂ)‖ = |r'| := by rw [Complex.norm_real, Real.norm_eq_abs]
    -- pointwise rewriting of the integrand
    have hptwise : ∀ θ : ℝ, Real.log (a - b * Real.cos θ)
        = (Real.log (|b| / 2) + Real.log ‖circleMap 0 1 θ - (r : ℂ)‖)
          + Real.log ‖circleMap 0 1 θ - (r' : ℂ)‖ := by
      intro θ
      have hz : ‖circleMap 0 1 θ‖ = 1 := by simp
      have hne : ∀ c : ℂ, ‖c‖ ≠ 1 → ‖circleMap 0 1 θ - c‖ ≠ 0 := by
        intro c hc
        simp only [ne_eq, norm_eq_zero, sub_eq_zero]
        intro h
        exact hc (by rw [← h]; simp [hz])
      have h1 : ‖circleMap 0 1 θ - (r : ℂ)‖ ≠ 0 :=
        hne _ (by rw [hnormr]; exact ne_of_gt hr_gt)
      have h2 : ‖circleMap 0 1 θ - (r' : ℂ)‖ ≠ 0 := by
        refine hne _ ?_
        rw [hnormr']
        intro hcon
        have : |r| * |r'| = 1 := by rw [← abs_mul, hrr']; simp
        rw [hcon, mul_one] at this
        rw [this] at hr_gt
        exact lt_irrefl _ hr_gt
      rw [sub_mul_cos_eq_norm_mul a b r r' hb0 hb hrr' hsum θ,
        Real.log_mul (by positivity) h2, Real.log_mul (by positivity) h1]
    rw [intervalIntegral.integral_congr (g := fun θ =>
      (Real.log (|b| / 2) + Real.log ‖circleMap 0 1 θ - (r : ℂ)‖)
        + Real.log ‖circleMap 0 1 θ - (r' : ℂ)‖) (fun θ _ => hptwise θ)]
    have hcont_r : Continuous fun θ : ℝ => Real.log ‖circleMap 0 1 θ - (r : ℂ)‖ :=
      continuous_log_norm_circleMap_sub _ (by rw [hnormr]; exact ne_of_gt hr_gt)
    have hcont_r' : Continuous fun θ : ℝ => Real.log ‖circleMap 0 1 θ - (r' : ℂ)‖ := by
      refine continuous_log_norm_circleMap_sub _ ?_
      rw [hnormr']
      intro hcon
      have h1 : |r| * |r'| = 1 := by rw [← abs_mul, hrr']; simp
      rw [hcon, mul_one] at h1
      rw [h1] at hr_gt
      exact lt_irrefl _ hr_gt
    have hint_c : IntervalIntegrable (fun _ : ℝ => Real.log (|b| / 2))
        MeasureTheory.volume 0 (2 * Real.pi) := continuous_const.intervalIntegrable _ _
    have hint_r : IntervalIntegrable (fun θ : ℝ => Real.log ‖circleMap 0 1 θ - (r : ℂ)‖)
        MeasureTheory.volume 0 (2 * Real.pi) := hcont_r.intervalIntegrable _ _
    have hint_r' : IntervalIntegrable (fun θ : ℝ => Real.log ‖circleMap 0 1 θ - (r' : ℂ)‖)
        MeasureTheory.volume 0 (2 * Real.pi) := hcont_r'.intervalIntegrable _ _
    rw [intervalIntegral.integral_add (hint_c.add hint_r) hint_r',
      intervalIntegral.integral_add hint_c hint_r,
      intervalIntegral.integral_const, integral_log_norm_circleMap_sub,
      integral_log_norm_circleMap_sub, hnormr, hnormr',
      Real.posLog_eq_log (by rw [abs_abs]; exact hr_gt.le),
      (Real.posLog_eq_zero_iff _).mpr (by rw [abs_abs]; exact habs_r'_le)]
    have hfinal : Real.log (|b| / 2) + Real.log |r| = Real.log ((a + s) / 2) := by
      rw [← Real.log_mul (by positivity) (by positivity), habs_r]
      congr 1
      field_simp
    simp only [smul_eq_mul, sub_zero, mul_zero, add_zero]
    rw [← hfinal]
    ring

/-! ## Main results -/

/-- At infinite temperature the partition function counts configurations: `Z = 2^(mn)`. -/
