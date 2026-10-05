/-
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Zeta23Scaffold

open MeasureTheory Set Real Filter Topology

/-! ### Laplace transform of `cos (a * x)` on `(0, ∞)` -/

/-- The function `x ↦ e^{-t x} cos (a x)` is integrable on `(0, ∞)` when `t > 0`. -/
theorem laplace_cos_integrableOn (t a : ℝ) (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => Real.exp (-(t * x)) * Real.cos (a * x)) (Ioi 0) := by
  apply MeasureTheory.Integrable.mono' (exp_neg_integrableOn_Ioi 0 ht)
  · exact ((Real.continuous_exp.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul, neg_mul]
    calc ‖Real.exp (-(t * x))‖ * ‖Real.cos (a * x)‖ ≤ ‖Real.exp (-(t * x))‖ * 1 := by
          gcongr; exact Real.abs_cos_le_one _
      _ = Real.exp (-(t * x)) := by simp [Real.exp_pos, abs_of_pos]

/-- The Laplace transform of the cosine: `∫_0^∞ e^{-t x} cos (a x) dx = t / (t² + a²)`. -/
theorem laplace_cos (t a : ℝ) (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), Real.exp (-(t * x)) * Real.cos (a * x) = t / (t ^ 2 + a ^ 2) := by
  have hden : (0 : ℝ) < t ^ 2 + a ^ 2 := by positivity
  set F : ℝ → ℝ := fun x =>
    Real.exp (-(t * x)) * (-t * Real.cos (a * x) + a * Real.sin (a * x)) / (t ^ 2 + a ^ 2) with hF
  have hderiv : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt F (Real.exp (-(t * x)) * Real.cos (a * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-(t * x))) (-t * Real.exp (-(t * x))) x := by
      have : HasDerivAt (fun x : ℝ => -(t * x)) (-t) x := by
        simpa using ((hasDerivAt_id x).const_mul t).neg
      simpa [mul_comm] using this.exp
    have h2 : HasDerivAt (fun x : ℝ => Real.cos (a * x)) (-(a * Real.sin (a * x))) x := by
      have : HasDerivAt (fun x : ℝ => a * x) a x := by simpa using (hasDerivAt_id x).const_mul a
      simpa [mul_comm] using this.cos
    have h3 : HasDerivAt (fun x : ℝ => Real.sin (a * x)) (a * Real.cos (a * x)) x := by
      have : HasDerivAt (fun x : ℝ => a * x) a x := by simpa using (hasDerivAt_id x).const_mul a
      simpa [mul_comm] using this.sin
    have h5 := ((h1.mul ((h2.const_mul (-t)).add (h3.const_mul a))).div_const (t ^ 2 + a ^ 2))
    convert h5 using 1
    simp only [Pi.add_apply]
    field_simp
    ring
  have htend : Tendsto F atTop (𝓝 0) := by
    have hb : Tendsto (fun x : ℝ => (t + |a|) / (t ^ 2 + a ^ 2) * Real.exp (-(t * x)))
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun x : ℝ => Real.exp (-(t * x))) atTop (𝓝 0) := by
        apply Real.tendsto_exp_atBot.comp
        exact Filter.tendsto_neg_atBot_iff.2 (Filter.Tendsto.const_mul_atTop ht tendsto_id)
      simpa using h0.const_mul ((t + |a|) / (t ^ 2 + a ^ 2))
    refine squeeze_zero_norm (fun x => ?_) hb
    have hN : |(-t * Real.cos (a * x) + a * Real.sin (a * x))| ≤ t + |a| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos ht]
      have h1 := Real.abs_cos_le_one (a * x)
      have h3 : |a| * |Real.sin (a * x)| ≤ |a| * 1 := by
        gcongr
        exact Real.abs_sin_le_one _
      nlinarith [abs_nonneg a, abs_nonneg (Real.cos (a * x))]
    rw [hF]
    simp only
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hden, abs_of_pos (Real.exp_pos _)]
    rw [div_le_iff₀ hden]
    calc Real.exp (-(t * x)) * |(-t * Real.cos (a * x) + a * Real.sin (a * x))|
        ≤ Real.exp (-(t * x)) * (t + |a|) := by gcongr
      _ = (t + |a|) / (t ^ 2 + a ^ 2) * Real.exp (-(t * x)) * (t ^ 2 + a ^ 2) := by field_simp
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (laplace_cos_integrableOn t a ht) htend
  rw [hres, hF]
  simp
  field_simp

/-- The Laplace transform of `sin⁴`: an explicit rational function of `t`. -/
theorem laplace_sin_fourth (t : ℝ) (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), Real.sin x ^ 4 * Real.exp (-(t * x))
      = 3 / (8 * t) - t / (2 * (t ^ 2 + 4)) + t / (8 * (t ^ 2 + 16)) := by
  have key : ∀ x : ℝ, Real.sin x ^ 4 * Real.exp (-(t * x))
      = (3 / 8 * (Real.exp (-(t * x)) * Real.cos (0 * x))
          - 1 / 2 * (Real.exp (-(t * x)) * Real.cos (2 * x)))
        + 1 / 8 * (Real.exp (-(t * x)) * Real.cos (4 * x)) := by
    intro x
    have h4 : (4 : ℝ) * x = 2 * (2 * x) := by ring
    rw [h4]
    simp only [Real.cos_two_mul, zero_mul, Real.cos_zero]
    have hs : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
      have := Real.sin_sq_add_cos_sq x; linarith
    rw [show Real.sin x ^ 4 = (Real.sin x ^ 2) ^ 2 by ring, hs]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => key x)]
  have hI1 : IntegrableOn
      (fun x : ℝ => 3 / 8 * (Real.exp (-(t * x)) * Real.cos (0 * x))) (Ioi 0) :=
    (laplace_cos_integrableOn t 0 ht).const_mul _
  have hI2 : IntegrableOn
      (fun x : ℝ => 1 / 2 * (Real.exp (-(t * x)) * Real.cos (2 * x))) (Ioi 0) :=
    (laplace_cos_integrableOn t 2 ht).const_mul _
  have hI3 : IntegrableOn
      (fun x : ℝ => 1 / 8 * (Real.exp (-(t * x)) * Real.cos (4 * x))) (Ioi 0) :=
    (laplace_cos_integrableOn t 4 ht).const_mul _
  have hI12 : IntegrableOn (fun x : ℝ => 3 / 8 * (Real.exp (-(t * x)) * Real.cos (0 * x))
      - 1 / 2 * (Real.exp (-(t * x)) * Real.cos (2 * x))) (Ioi 0) := hI1.sub hI2
  rw [MeasureTheory.integral_add hI12 hI3, MeasureTheory.integral_sub hI1 hI2,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul,
    laplace_cos t 0 ht, laplace_cos t 2 ht, laplace_cos t 4 ht]
  have h1 : t ^ 2 + (0 : ℝ) ^ 2 = t ^ 2 := by ring
  have h2 : t ^ 2 + (2 : ℝ) ^ 2 = t ^ 2 + 4 := by ring
  have h3 : t ^ 2 + (4 : ℝ) ^ 2 = t ^ 2 + 16 := by ring
  rw [h1, h2, h3]
  have htne : t ≠ 0 := ne_of_gt ht
  field_simp

/-- `t³ · (Laplace transform of sin⁴ at t)` simplifies to a difference of two Lorentzians. -/
theorem cube_mul_laplace_sin_fourth (t : ℝ) (ht : 0 < t) :
    t ^ 3 * (3 / (8 * t) - t / (2 * (t ^ 2 + 4)) + t / (8 * (t ^ 2 + 16)))
      = 32 * ((t ^ 2 + 4 ^ 2)⁻¹) - 8 * ((t ^ 2 + 2 ^ 2)⁻¹) := by
  have h1 : t ≠ 0 := ne_of_gt ht
  have h2 : t ^ 2 + 4 ≠ 0 := by positivity
  have h3 : t ^ 2 + 16 ≠ 0 := by positivity
  norm_num
  field_simp
  ring

/-! ### The Gamma-type integral `∫_0^∞ t³ e^{-x t} dt` -/

theorem integral_cube_mul_exp (x : ℝ) (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), t ^ 3 * Real.exp (-(x * t)) = 6 / x ^ 4 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 4) (r := x) (by norm_num) hx
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (f := fun t : ℝ => t ^ ((4 : ℝ) - 1) * Real.exp (-(x * t)))
    (g := fun t : ℝ => t ^ 3 * Real.exp (-(x * t))) ?_] at h
  · rw [h]
    have hg : Real.Gamma 4 = 6 := by
      have h3 := Real.Gamma_nat_eq_factorial 3
      norm_num at h3
      convert h3 using 2
      norm_num
    rw [hg]
    have hpow : ((1 : ℝ) / x) ^ (4 : ℝ) = (1 / x) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast (1 / x) 4]; norm_num
    rw [hpow]
    field_simp
  · intro t _
    simp only
    congr 1
    rw [show (4 : ℝ) - 1 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-! ### The Lorentzian integrals -/

theorem hasDerivAt_arctan_div (a : ℝ) (ha : 0 < a) :
    (∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun t : ℝ => Real.arctan (t / a) / a) ((x ^ 2 + a ^ 2)⁻¹) x) ∧
      Tendsto (fun t : ℝ => Real.arctan (t / a) / a) atTop (𝓝 ((π / 2) / a)) := by
  constructor
  · intro x _
    have h1 : HasDerivAt (fun t : ℝ => t / a) (1 / a) x := by
      simpa using (hasDerivAt_id x).div_const a
    have h3 := ((Real.hasDerivAt_arctan (x / a)).comp x h1).div_const a
    convert h3 using 1
    have hane : a ≠ 0 := ne_of_gt ha
    field_simp
    ring
  · have h0 : Tendsto (fun t : ℝ => t / a) atTop atTop :=
      Filter.Tendsto.atTop_div_const ha tendsto_id
    exact ((tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp h0).div_const a

theorem integrableOn_inv_sq_add (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => (t ^ 2 + a ^ 2)⁻¹) (Ioi 0) := by
  obtain ⟨hd, ht⟩ := hasDerivAt_arctan_div a ha
  exact integrableOn_Ioi_deriv_of_nonneg' hd (fun x _ => by positivity) ht

theorem integral_inv_sq_add (a : ℝ) (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), (t ^ 2 + a ^ 2)⁻¹ = π / (2 * a) := by
  obtain ⟨hd, ht⟩ := hasDerivAt_arctan_div a ha
  have := integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun x _ => by positivity) ht
  rw [this]
  simp [div_div]

/-- The `t`-side integral: `∫_0^∞ (32/(t²+16) - 8/(t²+4)) dt = 2π`. -/
theorem integral_lorentz_combo :
    ∫ t in Ioi (0 : ℝ), (32 * ((t ^ 2 + 4 ^ 2)⁻¹) - 8 * ((t ^ 2 + 2 ^ 2)⁻¹)) = 2 * π := by
  have h4 : IntegrableOn (fun t : ℝ => 32 * ((t ^ 2 + 4 ^ 2)⁻¹)) (Ioi 0) :=
    (integrableOn_inv_sq_add 4 (by norm_num)).const_mul _
  have h2 : IntegrableOn (fun t : ℝ => 8 * ((t ^ 2 + 2 ^ 2)⁻¹)) (Ioi 0) :=
    (integrableOn_inv_sq_add 2 (by norm_num)).const_mul _
  rw [MeasureTheory.integral_sub h4 h2, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, integral_inv_sq_add 4 (by norm_num),
    integral_inv_sq_add 2 (by norm_num)]
  ring

/-! ### The Fubini argument -/

/-- The two-variable integrand. -/
noncomputable def sincAux (x t : ℝ) : ℝ := t ^ 3 * Real.sin x ^ 4 * Real.exp (-(x * t))

theorem sin_pow_four_le_one (x : ℝ) : Real.sin x ^ 4 ≤ 1 := by
  have hs : Real.sin x ^ 2 ≤ 1 := Real.sin_sq_le_one x
  nlinarith [sq_nonneg (Real.sin x)]

theorem sincAux_integrableOn_x (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => sincAux x t) (Ioi 0) := by
  apply MeasureTheory.Integrable.mono' ((exp_neg_integrableOn_Ioi 0 ht).const_mul (t ^ 3))
  · apply Continuous.aestronglyMeasurable
    unfold sincAux
    fun_prop
  · filter_upwards with x
    unfold sincAux
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), show -(x * t) = -t * x by ring]
    calc t ^ 3 * Real.sin x ^ 4 * Real.exp (-t * x) ≤ t ^ 3 * 1 * Real.exp (-t * x) := by
          gcongr
          exact sin_pow_four_le_one x
      _ = t ^ 3 * Real.exp (-t * x) := by ring

theorem integral_norm_sincAux (t : ℝ) (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), ‖sincAux x t‖
      = 32 * ((t ^ 2 + 4 ^ 2)⁻¹) - 8 * ((t ^ 2 + 2 ^ 2)⁻¹) := by
  have hcongr : ∀ x ∈ Ioi (0 : ℝ),
      ‖sincAux x t‖ = t ^ 3 * (Real.sin x ^ 4 * Real.exp (-(t * x))) := by
    intro x _
    unfold sincAux
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), show -(x * t) = -(t * x) by ring]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr,
    MeasureTheory.integral_const_mul, laplace_sin_fourth t ht, cube_mul_laplace_sin_fourth t ht]

theorem sincAux_integrable_prod :
    Integrable (Function.uncurry sincAux)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry sincAux)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    apply Continuous.aestronglyMeasurable
    unfold Function.uncurry sincAux
    fun_prop
  rw [MeasureTheory.integrable_prod_iff' hmeas]
  constructor
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro t ht
    exact sincAux_integrableOn_x t ht
  · have hint : IntegrableOn
        (fun t : ℝ => 32 * ((t ^ 2 + 4 ^ 2)⁻¹) - 8 * ((t ^ 2 + 2 ^ 2)⁻¹)) (Ioi 0) :=
      ((integrableOn_inv_sq_add 4 (by norm_num)).const_mul _).sub
        ((integrableOn_inv_sq_add 2 (by norm_num)).const_mul _)
    refine hint.congr ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro t ht
    exact (integral_norm_sincAux t ht).symm

/-- The key half-line evaluation: `∫_0^∞ sin⁴x / x⁴ dx = π/3`. -/
theorem integral_sin_fourth_div_Ioi :
    ∫ x in Ioi (0 : ℝ), Real.sin x ^ 4 / x ^ 4 = π / 3 := by
  have hswap := MeasureTheory.integral_integral_swap
    (f := sincAux) sincAux_integrable_prod
  have hR : ∫ t in Ioi (0:ℝ), ∫ x in Ioi (0:ℝ), sincAux x t = 2 * π := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (g := fun t : ℝ => 32 * ((t ^ 2 + 4 ^ 2)⁻¹) - 8 * ((t ^ 2 + 2 ^ 2)⁻¹)) ?_]
    · exact integral_lorentz_combo
    · intro t ht
      have htp : (0:ℝ) < t := ht
      show (∫ x in Ioi (0:ℝ), sincAux x t) = 32 * ((t ^ 2 + 4 ^ 2)⁻¹) - 8 * ((t ^ 2 + 2 ^ 2)⁻¹)
      rw [← integral_norm_sincAux t htp]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro x _
      show t ^ 3 * Real.sin x ^ 4 * Real.exp (-(x * t))
          = ‖t ^ 3 * Real.sin x ^ 4 * Real.exp (-(x * t))‖
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (mul_nonneg (pow_nonneg htp.le 3) (by positivity)) (Real.exp_nonneg _))]
  have hL : ∫ x in Ioi (0:ℝ), ∫ t in Ioi (0:ℝ), sincAux x t
      = 6 * ∫ x in Ioi (0:ℝ), Real.sin x ^ 4 / x ^ 4 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    have hx' : (0:ℝ) < x := hx
    show (∫ t in Ioi (0:ℝ), sincAux x t) = 6 * (Real.sin x ^ 4 / x ^ 4)
    have hrw : ∀ t : ℝ, sincAux x t = Real.sin x ^ 4 * (t ^ 3 * Real.exp (-(x * t))) := by
      intro t; unfold sincAux; ring
    simp only [hrw]
    rw [MeasureTheory.integral_const_mul, integral_cube_mul_exp x hx']
    field_simp
  rw [hL, hR] at hswap
  linarith [hswap]

/-- **The main result.** `∫_ℝ (sin x / x)⁴ dx = 2π/3`. -/
theorem integral_sinc_fourth :
    ∫ x : ℝ, (Real.sin x / x) ^ 4 = 2 * Real.pi / 3 := by
  have hpt : ∀ x : ℝ, (Real.sin x / x) ^ 4
      = (fun y : ℝ => Real.sin y ^ 4 / y ^ 4) |x| := by
    intro x
    simp only
    rw [div_pow]
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h]
      rw [Real.sin_neg]
      ring
  calc ∫ x : ℝ, (Real.sin x / x) ^ 4
      = ∫ x : ℝ, (fun y : ℝ => Real.sin y ^ 4 / y ^ 4) |x| := by
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = 2 * ∫ x in Ioi (0 : ℝ), Real.sin x ^ 4 / x ^ 4 :=
        integral_comp_abs (f := fun y : ℝ => Real.sin y ^ 4 / y ^ 4)
    _ = 2 * Real.pi / 3 := by rw [integral_sin_fourth_div_Ioi]; ring

end Zeta23Scaffold

