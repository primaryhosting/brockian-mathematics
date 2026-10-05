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
lemma integral_sinc_sq_Ioi : ∫ x in Ioi (0:ℝ), (Real.sin x / x) ^ 2 = π / 2 := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (Real.sin x / x) ^ 2)
      (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi 0)] fun x : ℝ => (Real.sin x / x) ^ 2 := by
    filter_upwards with y using by positivity
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn hmeas]
  have hrw : (fun x : ℝ => ENNReal.ofReal ((Real.sin x / x) ^ 2))
      = fun x : ℝ => ENNReal.ofReal (Real.sin x ^ 2 / x ^ 2) := by
    funext x; rw [div_pow]
  rw [hrw, lintegral_sin_sq_div_sq, ENNReal.toReal_ofReal (by positivity)]

/-- **The normalization integral of the sine kernel**:
`∫_ℝ (sin x / x) ^ 2 dx = π`.

The integrand is understood as the Lebesgue-measurable function `x ↦ (sin x / x) ^ 2`, which
takes the value `0` at `x = 0` in Lean's convention; since `{0}` is a null set this agrees
almost everywhere with the continuous extension `x ↦ sinc x ^ 2` (see `integral_sinc_sq'`). -/
theorem integral_sinc_sq : ∫ x : ℝ, (Real.sin x / x) ^ 2 = π := by
  have hev : ∀ x : ℝ, (Real.sin x / x) ^ 2 = (Real.sin |x| / |x|) ^ 2 := by
    intro x
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, Real.sin_neg, neg_div_neg_eq]
  calc ∫ x : ℝ, (Real.sin x / x) ^ 2 = ∫ x : ℝ, (fun y : ℝ => (Real.sin y / y) ^ 2) |x| :=
        integral_congr_ae (Filter.Eventually.of_forall hev)
    _ = 2 * ∫ x in Ioi (0:ℝ), (Real.sin x / x) ^ 2 :=
        integral_comp_abs (f := fun y : ℝ => (Real.sin y / y) ^ 2)
    _ = π := by rw [integral_sinc_sq_Ioi]; ring

/-- The same statement for the continuous function `Real.sinc`, which equals `sin x / x`
for `x ≠ 0` and `1` at `x = 0`. -/
theorem integral_sinc_sq' : ∫ x : ℝ, (Real.sinc x) ^ 2 = π := by
  rw [← integral_sinc_sq]
  apply integral_congr_ae
  have h0 : ∀ᵐ (x : ℝ), x ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [h0] with x hx
  rw [Real.sinc_of_ne_zero hx]

end Zeta23Scaffold

import Mathlib

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

