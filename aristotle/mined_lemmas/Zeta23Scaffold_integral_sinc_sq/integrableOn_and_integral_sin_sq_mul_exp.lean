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

lemma integrableOn_and_integral_sin_sq_mul_exp (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => Real.sin x ^ 2 * Real.exp (-(t * x))) (Ioi 0) ∧
      ∫ x in Ioi (0:ℝ), Real.sin x ^ 2 * Real.exp (-(t * x)) = 2 / (t * (t ^ 2 + 4)) := by
  have ht4 : (0:ℝ) < t ^ 2 + 4 := by positivity
  set F : ℝ → ℝ := fun x => -Real.exp (-(t * x)) / (2 * t)
      + Real.exp (-(t * x)) * (t * Real.cos (2 * x) - 2 * Real.sin (2 * x)) / (2 * (t ^ 2 + 4))
    with hF
  have hderiv : ∀ x ∈ Ici (0:ℝ), HasDerivAt F (Real.sin x ^ 2 * Real.exp (-(t * x))) x := by
    intro x _
    have hsin : Real.sin x ^ 2 = (1 - Real.cos (2 * x)) / 2 := by
      rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq x]
    have hd : HasDerivAt (fun x : ℝ => -(t * x)) (-t) x := by
      simpa using ((hasDerivAt_id x).const_mul t).neg
    have hd2 : HasDerivAt (fun x : ℝ => 2 * x) 2 x := by
      simpa using (hasDerivAt_id x).const_mul 2
    have he : HasDerivAt (fun x : ℝ => Real.exp (-(t * x))) (Real.exp (-(t * x)) * (-t)) x := hd.exp
    have hc : HasDerivAt (fun x : ℝ => Real.cos (2 * x)) (-Real.sin (2 * x) * 2) x := hd2.cos
    have hs : HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (Real.cos (2 * x) * 2) x := hd2.sin
    have h0 : HasDerivAt F
        ((-(Real.exp (-(t * x)) * (-t))) / (2 * t)
         + (Real.exp (-(t * x)) * (-t) * (t * Real.cos (2 * x) - 2 * Real.sin (2 * x))
            + Real.exp (-(t * x)) * (t * (-Real.sin (2 * x) * 2)
              - 2 * (Real.cos (2 * x) * 2))) / (2 * (t ^ 2 + 4))) x :=
      (he.neg.div_const (2 * t)).add
        ((he.mul ((hc.const_mul t).sub (hs.const_mul 2))).div_const (2 * (t ^ 2 + 4)))
    convert h0 using 1
    show Real.sin x ^ 2 * Real.exp (-(t * x)) = _
    rw [hsin]
    field_simp
    ring
  have hnonneg : ∀ x ∈ Ioi (0:ℝ), 0 ≤ Real.sin x ^ 2 * Real.exp (-(t * x)) := by
    intro x _; positivity
  have htends : Tendsto F atTop (nhds 0) := by
    apply squeeze_zero_norm
      (a := fun x : ℝ => (1 / (2 * t) + (t + 2) / (2 * (t ^ 2 + 4))) * Real.exp (-(t * x)))
    · intro x
      have hpos : (0:ℝ) < Real.exp (-(t * x)) := Real.exp_pos _
      have hFx : F x = Real.exp (-(t * x))
          * (-(1 / (2 * t)) + (t * Real.cos (2 * x) - 2 * Real.sin (2 * x)) / (2 * (t ^ 2 + 4))) := by
        rw [hF]; field_simp
      have habs : |(-(1 / (2 * t))
            + (t * Real.cos (2 * x) - 2 * Real.sin (2 * x)) / (2 * (t ^ 2 + 4)))|
          ≤ 1 / (2 * t) + (t + 2) / (2 * (t ^ 2 + 4)) := by
        have hc := Real.neg_one_le_cos (2 * x)
        have hc' := Real.cos_le_one (2 * x)
        have hs := Real.neg_one_le_sin (2 * x)
        have hs' := Real.sin_le_one (2 * x)
        have h4 : (0:ℝ) < 2 * (t ^ 2 + 4) := by positivity
        rw [abs_le]
        constructor
        · rw [neg_le, ← sub_nonneg]
          have e : (1 / (2 * t) + (t + 2) / (2 * (t ^ 2 + 4)))
                - -(-(1 / (2 * t))
                  + (t * Real.cos (2 * x) - 2 * Real.sin (2 * x)) / (2 * (t ^ 2 + 4)))
              = (t * Real.cos (2 * x) - 2 * Real.sin (2 * x) + (t + 2)) / (2 * (t ^ 2 + 4)) := by
            field_simp; ring
          rw [e]
          apply div_nonneg _ h4.le
          nlinarith
        · rw [← sub_nonneg]
          have e : (1 / (2 * t) + (t + 2) / (2 * (t ^ 2 + 4)))
                - (-(1 / (2 * t))
                  + (t * Real.cos (2 * x) - 2 * Real.sin (2 * x)) / (2 * (t ^ 2 + 4)))
              = 1 / t + ((t + 2) - (t * Real.cos (2 * x) - 2 * Real.sin (2 * x)))
                  / (2 * (t ^ 2 + 4)) := by
            field_simp; ring
          rw [e]
          have h1 : (0:ℝ) ≤ 1 / t := by positivity
          have h2 : (0:ℝ) ≤ ((t + 2) - (t * Real.cos (2 * x) - 2 * Real.sin (2 * x)))
              / (2 * (t ^ 2 + 4)) := by
            apply div_nonneg _ h4.le
            nlinarith
          linarith
      rw [Real.norm_eq_abs, hFx, abs_mul, abs_of_pos hpos, mul_comm]
      exact mul_le_mul_of_nonneg_right habs hpos.le
    · have h1 : Tendsto (fun x : ℝ => t * x) atTop atTop :=
        Filter.Tendsto.const_mul_atTop ht tendsto_id
      have h2 : Tendsto (fun x : ℝ => Real.exp (-(t * x))) atTop (nhds 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
      simpa using h2.const_mul (1 / (2 * t) + (t + 2) / (2 * (t ^ 2 + 4)))
  refine ⟨MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hderiv hnonneg htends, ?_⟩
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnonneg htends, hF]
  simp only [mul_zero, neg_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero]
  field_simp
  ring

/-- The elementary arctangent integral `∫_0^∞ 2 / (t ^ 2 + 4) dt = π / 2`. -/
