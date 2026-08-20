import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

theorem real_scaled_power_of_deriv_bound {x y : ℝ} (hx_large : (4840 : ℝ) ≤ x)
    (hy_lower : (5 : ℝ) / 2 * x ≤ y)
    (hderiv : ∀ z ∈ Set.Icc (((5 : ℝ) / 2) * x) y, √z * (2 + log z) ≤ 2 * x) :
    x * y ^ √y < (y / (2 * x)) ^ x := by
  let a : ℝ := (5 : ℝ) / 2 * x
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hx_large
  have ha : 0 < a := by dsimp [a]; positivity
  have hy : 0 < y := lt_of_lt_of_le ha (by simpa [a] using hy_lower)
  have hcont : ContinuousOn (fun t => scaledPowerLog x t) (Set.Icc a y) := by
    unfold scaledPowerLog
    have hid : ContinuousOn (fun t : ℝ => t) (Set.Icc a y) := continuous_id.continuousOn
    have hlogt : ContinuousOn (fun t : ℝ => log t) (Set.Icc a y) :=
      hid.log (fun t ht => by nlinarith [ha, ht.1])
    have hdiv : ContinuousOn (fun t : ℝ => t / (2 * x)) (Set.Icc a y) := by
      exact hid.div continuous_const.continuousOn (fun _ _ => by positivity)
    have hlogdiv : ContinuousOn (fun t : ℝ => log (t / (2 * x))) (Set.Icc a y) :=
      hdiv.log (fun t ht => by
        have htpos : 0 < t := by nlinarith [ha, ht.1]
        exact (div_pos htpos (mul_pos two_pos hx)).ne')
    exact (continuous_const.continuousOn.add (hid.sqrt.mul hlogt)).sub
      (continuous_const.continuousOn.mul hlogdiv)
  have hdiff : DifferentiableOn ℝ (fun t => scaledPowerLog x t) (interior (Set.Icc a y)) := by
    intro z hz
    have hzIcc : z ∈ Set.Icc a y := interior_subset hz
    have hzpos : 0 < z := by nlinarith [ha, hzIcc.1]
    exact (hasDerivAt_scaledPowerLog hx hzpos).differentiableAt.differentiableWithinAt
  have hnonpos : ∀ z ∈ interior (Set.Icc a y), deriv (fun t => scaledPowerLog x t) z ≤ 0 := by
    intro z hz
    have hzIcc : z ∈ Set.Icc a y := interior_subset hz
    have hzpos : 0 < z := by nlinarith [ha, hzIcc.1]
    exact deriv_scaledPowerLog_nonpos hx hzpos (hderiv z hzIcc)
  have hanti : AntitoneOn (fun t => scaledPowerLog x t) (Set.Icc a y) :=
    antitoneOn_of_deriv_nonpos (convex_Icc a y) hcont hdiff hnonpos
  have ha_mem : a ∈ Set.Icc a y := ⟨le_rfl, by simpa [a] using hy_lower⟩
  have hy_mem : y ∈ Set.Icc a y := ⟨by simpa [a] using hy_lower, le_rfl⟩
  have hlog_le : scaledPowerLog x y ≤ scaledPowerLog x a :=
    hanti ha_mem hy_mem (by simpa [a] using hy_lower)
  have hboundary : scaledPowerLog x a < 0 := by
    have hb := real_scaled_power_boundary_five_halves (x := x) hx_large
    have hratio_pos : 0 < x * a ^ √a / (a / (2 * x)) ^ x := by positivity
    rw [scaledPowerLog_eq_log_ratio hx ha, log_neg_iff hratio_pos]
    have ha_eq : a / (2 * x) = (5 : ℝ) / 4 := by
      dsimp [a]
      field_simp [(ne_of_gt hx)]
      ring
    rw [ha_eq, div_lt_one (rpow_pos_of_pos (by norm_num : (0 : ℝ) < 5 / 4) x)]
    simpa [a] using hb
  have hlog_neg : scaledPowerLog x y < 0 := lt_of_le_of_lt hlog_le hboundary
  have hratio_pos : 0 < x * y ^ √y / (y / (2 * x)) ^ x := by positivity
  rw [scaledPowerLog_eq_log_ratio hx hy, log_neg_iff hratio_pos] at hlog_neg
  rwa [div_lt_one (rpow_pos_of_pos (div_pos hy (mul_pos two_pos hx)) x)] at hlog_neg

