/-
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` only because Lean 4 requires `import`
-- commands to precede every module docstring; the text is otherwise verbatim.)

import Mathlib

open Real Filter MeasureTheory Set

namespace Zeta23Scaffold

/-- For `x > 0`, the function `t ↦ t * exp (-(t * x))` is integrable on `(0, ∞)` and its
integral there equals `1 / x ^ 2`. -/

lemma integrableOn_and_integral_two_div_sq_add_four :
    IntegrableOn (fun t : ℝ => 2 / (t ^ 2 + 4)) (Ioi 0) ∧
      ∫ t in Ioi (0:ℝ), 2 / (t ^ 2 + 4) = π / 2 := by
  have hderiv : ∀ t ∈ Ici (0:ℝ), HasDerivAt (fun t : ℝ => Real.arctan (t / 2))
      (2 / (t ^ 2 + 4)) t := by
    intro t _
    have hd : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) t := by
      simpa using (hasDerivAt_id t).div_const 2
    have h := hd.arctan
    convert h using 1
    have h2 : (0:ℝ) < 1 + (t / 2) ^ 2 := by positivity
    field_simp
    ring
  have hnonneg : ∀ t ∈ Ioi (0:ℝ), 0 ≤ 2 / (t ^ 2 + 4) := by intro t _; positivity
  have htends : Tendsto (fun t : ℝ => Real.arctan (t / 2)) atTop (nhds (π / 2)) := by
    have h1 : Tendsto (fun t : ℝ => t / 2) atTop atTop := by
      simpa using Filter.tendsto_id.atTop_div_const (by norm_num : (0:ℝ) < 2)
    exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1
  refine ⟨MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hderiv hnonneg htends, ?_⟩
  simpa using MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnonneg htends

/-- Tonelli's theorem applied to `sin x ^ 2 / x ^ 2 = ∫_0^∞ sin x ^ 2 * t * exp (-t x) dt`. -/
