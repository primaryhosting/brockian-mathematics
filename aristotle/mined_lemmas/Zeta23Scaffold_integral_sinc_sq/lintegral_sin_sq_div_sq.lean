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

lemma lintegral_sin_sq_div_sq :
    ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (Real.sin x ^ 2 / x ^ 2) = ENNReal.ofReal (π / 2) := by
  have hae : ∀ g : ℝ → ℝ, (∀ y ∈ Ioi (0:ℝ), 0 ≤ g y) →
      (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi 0)] g := by
    intro g h
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy using h y hy
  -- Rewrite `sin x ^ 2 / x ^ 2` as an inner integral over the parameter `t`.
  have step1 : EqOn (fun x : ℝ => ENNReal.ofReal (Real.sin x ^ 2 / x ^ 2))
      (fun x : ℝ => ∫⁻ t in Ioi (0:ℝ),
        ENNReal.ofReal (Real.sin x ^ 2 * (t * Real.exp (-(t * x))))) (Ioi 0) := by
    intro x hx
    have hx' : (0:ℝ) < x := hx
    obtain ⟨hint, hval⟩ := integrableOn_and_integral_mul_exp x hx'
    have h0 := hae (fun t => Real.sin x ^ 2 * (t * Real.exp (-(t * x)))) (by
      intro t ht
      have ht' : (0:ℝ) ≤ t := le_of_lt ht
      positivity)
    show ENNReal.ofReal (Real.sin x ^ 2 / x ^ 2)
        = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (Real.sin x ^ 2 * (t * Real.exp (-(t * x))))
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint.const_mul _) h0,
      MeasureTheory.integral_const_mul, hval]
    congr 1
    field_simp
  rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi step1]
  -- Tonelli: swap the order of integration.
  rw [MeasureTheory.lintegral_lintegral_swap (by
    apply Measurable.aemeasurable
    unfold Function.uncurry
    fun_prop)]
  -- Evaluate the inner integral over `x`.
  have step3 : EqOn (fun t : ℝ => ∫⁻ x in Ioi (0:ℝ),
        ENNReal.ofReal (Real.sin x ^ 2 * (t * Real.exp (-(t * x)))))
      (fun t : ℝ => ENNReal.ofReal (2 / (t ^ 2 + 4))) (Ioi 0) := by
    intro t ht
    have ht' : (0:ℝ) < t := ht
    obtain ⟨hint, hval⟩ := integrableOn_and_integral_sin_sq_mul_exp t ht'
    have h0 := hae (fun x => t * (Real.sin x ^ 2 * Real.exp (-(t * x)))) (by
      intro x _
      have : (0:ℝ) ≤ t := ht'.le
      positivity)
    show (∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (Real.sin x ^ 2 * (t * Real.exp (-(t * x)))))
        = ENNReal.ofReal (2 / (t ^ 2 + 4))
    have hrw : (fun x : ℝ => ENNReal.ofReal (Real.sin x ^ 2 * (t * Real.exp (-(t * x)))))
        = fun x : ℝ => ENNReal.ofReal (t * (Real.sin x ^ 2 * Real.exp (-(t * x)))) := by
      funext x; ring_nf
    simp only [hrw]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint.const_mul _) h0,
      MeasureTheory.integral_const_mul, hval]
    congr 1
    field_simp
  rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi step3]
  obtain ⟨hint3, hval3⟩ := integrableOn_and_integral_two_div_sq_add_four
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint3 (hae _ (by
    intro t _; positivity)), hval3]

/-- The half-line version: `∫_0^∞ (sin x / x) ^ 2 dx = π / 2`. -/
