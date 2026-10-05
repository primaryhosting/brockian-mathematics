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

lemma integrableOn_and_integral_mul_exp (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(t * x))) (Ioi 0) ∧
      ∫ t in Ioi (0:ℝ), t * Real.exp (-(t * x)) = 1 / x ^ 2 := by
  set G : ℝ → ℝ := fun t => -((t * x + 1) * Real.exp (-(t * x))) / x ^ 2 with hG
  have hderiv : ∀ t ∈ Ici (0:ℝ), HasDerivAt G (t * Real.exp (-(t * x))) t := by
    intro t _
    have h : HasDerivAt G
        (-((1 * x) * Real.exp (-(t * x))
          + (t * x + 1) * (Real.exp (-(t * x)) * (-(1 * x)))) / x ^ 2) t := by
      apply HasDerivAt.div_const
      apply HasDerivAt.neg
      exact HasDerivAt.mul (((hasDerivAt_id t).mul_const x).add_const 1)
        (((hasDerivAt_id t).mul_const x).neg.exp)
    convert h using 1
    field_simp
    ring
  have hnonneg : ∀ t ∈ Ioi (0:ℝ), 0 ≤ t * Real.exp (-(t * x)) := fun t ht =>
    mul_nonneg (le_of_lt ht) (Real.exp_pos _).le
  have htends : Tendsto G atTop (nhds 0) := by
    have h1 : Tendsto (fun t : ℝ => t * x) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hx tendsto_id
    have h2 : Tendsto (fun u : ℝ => -((u + 1) * Real.exp (-u)) / x ^ 2) atTop (nhds 0) := by
      have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
      have h3 := Real.tendsto_exp_neg_atTop_nhds_zero
      have h4 : Tendsto (fun u : ℝ => (u + 1) * Real.exp (-u)) atTop (nhds 0) := by
        simpa [add_mul] using h0.add h3
      simpa [neg_div] using (h4.neg).div_const (x ^ 2)
    exact h2.comp h1
  refine ⟨MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hderiv hnonneg htends, ?_⟩
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnonneg htends, hG]
  simp
  field_simp

/-- For `t > 0`, the function `x ↦ sin x ^ 2 * exp (-(t * x))` is integrable on `(0, ∞)` and its
integral there equals `2 / (t * (t ^ 2 + 4))`. -/
