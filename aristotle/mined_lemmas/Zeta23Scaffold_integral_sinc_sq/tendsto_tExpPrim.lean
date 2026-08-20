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

lemma tendsto_tExpPrim {x : ℝ} (hx : 0 < x) :
    Tendsto (tExpPrim x) atTop (𝓝 0) := by
  have hmul : Tendsto (fun t : ℝ => t * x) atTop atTop := tendsto_id.atTop_mul_const hx
  have hneg : Tendsto (fun t : ℝ => -(t * x)) atTop atBot := tendsto_neg_atBot_iff.mpr hmul
  have h0 : Tendsto (fun u : ℝ => u * Real.exp (-u)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h1 : Tendsto (fun t : ℝ => (t * x) * Real.exp (-(t * x))) atTop (𝓝 0) := h0.comp hmul
  have h2 : Tendsto (fun t : ℝ => Real.exp (-(t * x))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have h := (h1.const_mul (-(1 / x ^ 2))).add (h2.const_mul (-(1 / x ^ 2)))
  simp only [mul_zero, add_zero] at h
  refine h.congr (fun t => ?_)
  have hx' : x ≠ 0 := ne_of_gt hx
  unfold tExpPrim
  field_simp
  ring

