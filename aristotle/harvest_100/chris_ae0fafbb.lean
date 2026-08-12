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
noncomputable def sincKer (x t : ℝ) : ℝ := t * Real.sin x ^ 2 * Real.exp (-(t * x))

lemma sincKer_nonneg {x t : ℝ} (ht : 0 ≤ t) : 0 ≤ sincKer x t := by
  have := Real.exp_pos (-(t * x))
  have : (0:ℝ) ≤ Real.sin x ^ 2 := sq_nonneg _
  unfold sincKer
  positivity

lemma continuous_sincKer : Continuous fun p : ℝ × ℝ => sincKer p.1 p.2 := by
  unfold sincKer
  fun_prop

/-! ### The `t`-integral: `∫_0^∞ t e^{-tx} dt = 1/x²` -/

/-- Antiderivative in `t` of `t * exp (-(t * x))`. -/
noncomputable def tExpPrim (x t : ℝ) : ℝ := -(t / x + 1 / x ^ 2) * Real.exp (-(t * x))

lemma hasDerivAt_tExpPrim {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (tExpPrim x) (t * Real.exp (-(t * x))) t := by
  have hlin : HasDerivAt (fun t : ℝ => -(t * x)) (-x) t := by
    simpa using ((hasDerivAt_id t).mul_const x).neg
  have h1 : HasDerivAt (fun t : ℝ => -(t / x + 1 / x ^ 2)) (-(1 / x)) t := by
    have h0 := (((hasDerivAt_id t).div_const x).add_const (1 / x ^ 2)).neg
    exact h0.congr_deriv (by simp)
  have h3 := h1.mul hlin.exp
  refine h3.congr_deriv ?_
  have hx' : x ≠ 0 := ne_of_gt hx
  field_simp
  ring

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

lemma nonneg_t_mul_exp {x : ℝ} : ∀ t ∈ Ioi (0:ℝ), 0 ≤ t * Real.exp (-(t * x)) := fun _ ht =>
  mul_nonneg (le_of_lt (mem_Ioi.mp ht)) (Real.exp_pos _).le

/-- `∫_0^∞ t e^{-tx} dt = 1/x²` for `x > 0`. -/
lemma integral_t_mul_exp {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-(t * x)) = 1 / x ^ 2 := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t _ => hasDerivAt_tExpPrim hx t) nonneg_t_mul_exp (tendsto_tExpPrim hx)
  rw [h]
  simp [tExpPrim]

lemma integrableOn_t_mul_exp {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(t * x))) (Ioi 0) :=
  MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
    (fun t _ => hasDerivAt_tExpPrim hx t) nonneg_t_mul_exp (tendsto_tExpPrim hx)

lemma sincKer_eq_mul (x t : ℝ) : sincKer x t = Real.sin x ^ 2 * (t * Real.exp (-(t * x))) := by
  unfold sincKer; ring

lemma integral_sincKer_t {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), sincKer x t = (Real.sin x / x) ^ 2 := by
  simp_rw [sincKer_eq_mul]
  rw [MeasureTheory.integral_const_mul, integral_t_mul_exp hx]
  field_simp

lemma integrableOn_sincKer_t {x : ℝ} (hx : 0 < x) :
    IntegrableOn (sincKer x) (Ioi 0) := by
  have h : sincKer x = fun t : ℝ => Real.sin x ^ 2 * (t * Real.exp (-(t * x))) :=
    funext (sincKer_eq_mul x)
  rw [h]
  exact (integrableOn_t_mul_exp hx).const_mul _

/-! ### The `x`-integral: `∫_0^∞ t sin²x e^{-tx} dx = 2/(t²+4)` -/

/-- Antiderivative in `x` of `t * sin x ^ 2 * exp (-(t * x))`. -/
noncomputable def sinSqExpPrim (t x : ℝ) : ℝ :=
  Real.exp (-(t * x)) * (-1 / 2 - t * (-t * Real.cos (2 * x) + 2 * Real.sin (2 * x)) / (2 * (t ^ 2 + 4)))

lemma hasDerivAt_sinSqExpPrim (t x : ℝ) :
    HasDerivAt (sinSqExpPrim t) (sincKer x t) x := by
  have hl : HasDerivAt (fun x : ℝ => -(t * x)) (-t) x := by
    simpa using ((hasDerivAt_id x).const_mul t).neg
  have he : HasDerivAt (fun x : ℝ => Real.exp (-(t * x))) (Real.exp (-(t * x)) * (-t)) x := hl.exp
  have h2x : HasDerivAt (fun x : ℝ => 2 * x) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  have hc : HasDerivAt (fun x : ℝ => Real.cos (2 * x)) (-Real.sin (2 * x) * 2) x := h2x.cos
  have hs : HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (Real.cos (2 * x) * 2) x := h2x.sin
  have hA : HasDerivAt
      (fun x : ℝ => -1 / 2 - t * (-t * Real.cos (2 * x) + 2 * Real.sin (2 * x)) / (2 * (t ^ 2 + 4)))
      (-(t * (-t * (-Real.sin (2 * x) * 2) + 2 * (Real.cos (2 * x) * 2)) / (2 * (t ^ 2 + 4)))) x := by
    have h := (((hc.const_mul (-t)).add (hs.const_mul 2)).const_mul t).div_const (2 * (t ^ 2 + 4))
    exact (h.const_sub (-1 / 2 : ℝ)).congr_deriv (by ring)
  refine (he.mul hA).congr_deriv ?_
  have h4 : (2 : ℝ) * (t ^ 2 + 4) ≠ 0 := by positivity
  have hsin : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := Real.sin_two_mul x
  have hcos : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
    rw [Real.cos_two_mul']; nlinarith [Real.sin_sq_add_cos_sq x]
  simp only [sincKer, hsin, hcos]
  field_simp
  ring

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
lemma integral_sincKer_x {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), sincKer x t = 2 / (t ^ 2 + 4) := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
    (fun x _ => hasDerivAt_sinSqExpPrim t x)
    (fun x _ => sincKer_nonneg ht.le) (tendsto_sinSqExpPrim ht)
  rw [h]
  have h4 : (t : ℝ) ^ 2 + 4 ≠ 0 := by positivity
  simp only [sinSqExpPrim, mul_zero, neg_zero, Real.exp_zero, one_mul, Real.cos_zero,
    Real.sin_zero]
  field_simp
  ring

lemma integrableOn_sincKer_x {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => sincKer x t) (Ioi 0) :=
  MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
    (fun x _ => hasDerivAt_sinSqExpPrim t x)
    (fun _ _ => sincKer_nonneg ht.le) (tendsto_sinSqExpPrim ht)

/-! ### The outer integral -/

lemma hasDerivAt_arctan_half (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.arctan (t / 2)) (2 / (t ^ 2 + 4)) t := by
  have h1 : HasDerivAt (fun t : ℝ => t / 2) (1 / 2 : ℝ) t := by
    simpa using (hasDerivAt_id t).div_const 2
  refine h1.arctan.congr_deriv ?_
  have h2 : (t / 2) ^ 2 + 1 > 0 := by positivity
  field_simp
  ring

lemma tendsto_arctan_half : Tendsto (fun t : ℝ => Real.arctan (t / 2)) atTop (𝓝 (π / 2)) := by
  have h2 : Tendsto (fun t : ℝ => t / 2) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h2

lemma integral_two_div_sq_add_four :
    ∫ t in Ioi (0 : ℝ), 2 / (t ^ 2 + 4) = π / 2 := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
    (fun t _ => hasDerivAt_arctan_half t) (fun t (_ : t ∈ Ioi (0:ℝ)) => by positivity)
    tendsto_arctan_half
  simpa using h

lemma integrableOn_two_div_sq_add_four :
    IntegrableOn (fun t : ℝ => 2 / (t ^ 2 + 4)) (Ioi 0) :=
  MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
    (fun t _ => hasDerivAt_arctan_half t) (fun t _ => by positivity) tendsto_arctan_half

/-! ### Tonelli and conclusion -/

/-- The half-line version: `∫_0^∞ (sin x / x)² dx = π/2`, obtained from Tonelli's theorem
applied to the kernel `sincKer`. -/
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
theorem integral_sinc_sq : ∫ x : ℝ, (Real.sin x / x) ^ 2 = π := by
  have habs : ∀ x : ℝ, (Real.sin |x| / |x|) ^ 2 = (Real.sin x / x) ^ 2 := by
    intro x
    rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
    rw [Real.sin_neg, neg_div_neg_eq]
  calc ∫ x : ℝ, (Real.sin x / x) ^ 2 = ∫ x : ℝ, (fun y : ℝ => (Real.sin y / y) ^ 2) |x| := by
        simp only [habs]
    _ = 2 * ∫ x in Ioi (0:ℝ), (Real.sin x / x) ^ 2 :=
        integral_comp_abs (f := fun y : ℝ => (Real.sin y / y) ^ 2)
    _ = π := by rw [integral_sinc_sq_Ioi]; ring

/-- Version stated with the continuous `Real.sinc` function. -/
theorem integral_sinc_sq' : ∫ x : ℝ, Real.sinc x ^ 2 = π := by
  have hae : ∀ᵐ x : ℝ, Real.sinc x ^ 2 = (Real.sin x / x) ^ 2 := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (fun x hx => ?_) (Real.volume_singleton (a := (0:ℝ)))
    simp only [mem_singleton_iff]
    by_contra hne
    exact hx (by rw [Real.sinc_of_ne_zero hne])
  rw [MeasureTheory.integral_congr_ae hae, integral_sinc_sq]

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

