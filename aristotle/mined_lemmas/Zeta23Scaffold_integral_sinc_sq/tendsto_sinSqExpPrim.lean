import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Set Filter Real
open scoped Topology ENNReal

namespace Zeta23Scaffold

/-- The auxiliary kernel `t * sin x ^ 2 * exp (-(t * x))`, used to compute the integral of
`(sin x / x) ^ 2` by Tonelli's theorem, via `1 / x ^ 2 = ∫ t in (0, ∞), t * exp (-(t * x))`. -/

lemma tendsto_sinSqExpPrim {t : ℝ} (ht : 0 < t) :
    Tendsto (sinSqExpPrim t) atTop (𝓝 0) := by
  have hmul : Tendsto (fun x : ℝ => t * x) atTop atTop := tendsto_id.const_mul_atTop ht
  have hb1 : Tendsto (fun x : ℝ => Real.exp (-(t * x))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr hmul)
  have hb2 : Tendsto (fun x : ℝ => Real.exp (-(t * x)) * Real.cos (2 * x)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun x => ?_) hb1
    rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(t * x)) * ‖Real.cos (2 * x)‖ ≤ Real.exp (-(t * x)) * 1 := by
          gcongr; simpa using Real.abs_cos_le_one (2 * x)
      _ = Real.exp (-(t * x)) := by ring
  have hb3 : Tendsto (fun x : ℝ => Real.exp (-(t * x)) * Real.sin (2 * x)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun x => ?_) hb1
    rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(t * x)) * ‖Real.sin (2 * x)‖ ≤ Real.exp (-(t * x)) * 1 := by
          gcongr; simpa using Real.abs_sin_le_one (2 * x)
      _ = Real.exp (-(t * x)) := by ring
  have h := (hb1.const_mul (-1 / 2 : ℝ)).add ((hb2.const_mul (t ^ 2 / (2 * (t ^ 2 + 4)))).sub
    (hb3.const_mul (t / (t ^ 2 + 4))))
  simp only [mul_zero, add_zero, sub_zero] at h
  refine h.congr (fun x => ?_)
  have h4 : (2 : ℝ) * (t ^ 2 + 4) ≠ 0 := by positivity
  unfold sinSqExpPrim
  field_simp
  ring

/-- `∫_0^∞ t sin²x e^{-tx} dx = 2/(t²+4)` for `t > 0`. -/
