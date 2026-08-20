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

lemma integral_sinc_sq_Ioi :
    ∫ x in Ioi (0 : ℝ), (Real.sin x / x) ^ 2 = π / 2 := by
  have hmeas : AEMeasurable (Function.uncurry fun x t => ENNReal.ofReal (sincKer x t))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) :=
    (ENNReal.continuous_ofReal.comp continuous_sincKer).measurable.aemeasurable
  have hswap := MeasureTheory.lintegral_lintegral_swap hmeas
  have hL : ∫⁻ x in Ioi (0:ℝ), ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (sincKer x t)
      = ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal ((Real.sin x / x) ^ 2) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx' : 0 < x := mem_Ioi.mp hx
    have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi (0:ℝ))] sincKer x :=
      (ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun t ht => sincKer_nonneg (le_of_lt (mem_Ioi.mp ht)))
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrableOn_sincKer_t hx') hnn,
      integral_sincKer_t hx']
  have hR : ∫⁻ t in Ioi (0:ℝ), ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (sincKer x t)
      = ENNReal.ofReal (π / 2) := by
    have h1 : ∫⁻ t in Ioi (0:ℝ), ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (sincKer x t)
        = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (2 / (t ^ 2 + 4)) := by
      refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have ht' : 0 < t := mem_Ioi.mp ht
      have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi (0:ℝ))] (fun x => sincKer x t) :=
        Eventually.of_forall fun x => sincKer_nonneg ht'.le
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrableOn_sincKer_x ht') hnn,
        integral_sincKer_x ht']
    rw [h1, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal integrableOn_two_div_sq_add_four
      (Eventually.of_forall fun t => by positivity), integral_two_div_sq_add_four]
  have key : ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal ((Real.sin x / x) ^ 2) = ENNReal.ofReal (π / 2) := by
    rw [← hL, hswap, hR]
  have hm : Measurable (fun x : ℝ => (Real.sin x / x) ^ 2) :=
    (Real.measurable_sin.div measurable_id).pow_const 2
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => by positivity) hm.aestronglyMeasurable, key,
    ENNReal.toReal_ofReal (by positivity)]

/-- The Dirichlet-type integral: `∫_ℝ (sin x / x)² dx = π`.
(The integrand takes the junk value `sin 0 / 0 = 0` at the origin, a null set; it agrees a.e.
with the continuous extension `Real.sinc`, see `Zeta23Scaffold.integral_sinc_sq'`.) -/
