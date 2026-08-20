/-
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open MeasureTheory Set Real

namespace Brockian
namespace DilationGenerator

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The substitution operator `U : (U f)(t) = e^{t/2} · f(eᵗ)`, at the level of functions. -/
noncomputable def logSub (f : ℝ → F) : ℝ → F := fun t => Real.exp (t / 2) • f (Real.exp t)

/-- The inverse substitution `U⁻¹ : (U⁻¹ h)(x) = x^{-1/2} · h(log x)`, at the level of
functions. -/
noncomputable def logSubSymm (h : ℝ → F) : ℝ → F :=
  fun x => (x ^ (-(1 : ℝ) / 2) : ℝ) • h (Real.log x)

/-- **Change of variables `x = eᵗ`.** For any function `g : ℝ → F` (no integrability or
measurability assumption is needed: both sides are `0` when the integrand is not integrable),
the integral of `g` over `(0, ∞)` equals the integral of `eᵗ • g (eᵗ)` over `ℝ`. -/
theorem integral_Ioi_eq_integral_exp_smul (g : ℝ → F) :
    ∫ x in Ioi (0 : ℝ), g x = ∫ t : ℝ, Real.exp t • g (Real.exp t) := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := Real.exp) (f' := Real.exp)
    (s := (univ : Set ℝ)) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g
  rw [image_univ, Real.range_exp] at h
  simpa only [Measure.restrict_univ, abs_of_pos (Real.exp_pos _)] using h

/-- **The substitution `x = eᵗ` is `L²`-norm preserving.**

The map `f ↦ (fun t => e^{t/2} • f (eᵗ))` sends a function on `(0, ∞)` to a function on `ℝ`
with the same `L²` integral:
`∫_{(0,∞)} ‖f x‖² dx = ∫_ℝ ‖e^{t/2} • f (eᵗ)‖² dt`.
This is the integral identity underlying the unitary `U : L²(0, ∞) ≃ L²(ℝ)` of the Mellin
(logarithmic) change of variables. No hypotheses on `f` are required. -/
theorem mellin_log_unitary (f : ℝ → F) :
    ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 = ∫ t : ℝ, ‖Real.exp (t / 2) • f (Real.exp t)‖ ^ 2 := by
  rw [integral_Ioi_eq_integral_exp_smul (fun x => ‖f x‖ ^ 2)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hexp : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [← Real.exp_nat_mul]; norm_num; ring
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, smul_eq_mul,
    hexp]

/-- Scalar cancellation: `e^{t/2} · (eᵗ)^{-1/2} = 1`. -/
private lemma exp_half_mul_rpow_neg_half (t : ℝ) :
    Real.exp (t / 2) * (Real.exp t) ^ (-(1 : ℝ) / 2) = 1 := by
  rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp, ← Real.exp_add]
  have : t / 2 + t * (-(1 : ℝ) / 2) = 0 := by ring
  rw [this, Real.exp_zero]

/-- Scalar cancellation: `x^{-1/2} · e^{(log x)/2} = 1` for `0 < x`. -/
private lemma rpow_neg_half_mul_exp_half {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 : ℝ) / 2) * Real.exp (Real.log x / 2) = 1 := by
  rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
  have : Real.log x * (-(1 : ℝ) / 2) + Real.log x / 2 = 0 := by ring
  rw [this, Real.exp_zero]

/-- The inverse substitution `t = log x` is also `L²`-norm preserving:
`∫_ℝ ‖h t‖² dt = ∫_{(0,∞)} ‖x^{-1/2} • h (log x)‖² dx`. -/
theorem mellin_log_unitary_symm (h : ℝ → F) :
    ∫ t : ℝ, ‖h t‖ ^ 2
      = ∫ x in Ioi (0 : ℝ), ‖(x ^ (-(1 : ℝ) / 2) : ℝ) • h (Real.log x)‖ ^ 2 := by
  rw [mellin_log_unitary (fun x => (x ^ (-(1 : ℝ) / 2) : ℝ) • h (Real.log x))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Real.log_exp, smul_smul, exp_half_mul_rpow_neg_half t, one_smul]

/-- The two substitutions are mutually inverse: `U⁻¹ (U f) = f` on `(0, ∞)`. -/
theorem logSubSymm_logSub (f : ℝ → F) {x : ℝ} (hx : 0 < x) : logSubSymm (logSub f) x = f x := by
  simp only [logSub, logSubSymm, smul_smul, Real.exp_log hx, rpow_neg_half_mul_exp_half hx,
    one_smul]

/-- The two substitutions are mutually inverse: `U (U⁻¹ h) = h` on `ℝ`. -/
theorem logSub_logSubSymm (h : ℝ → F) : logSub (logSubSymm h) = h := by
  funext t
  simp only [logSub, logSubSymm, Real.log_exp, smul_smul, exp_half_mul_rpow_neg_half t, one_smul]

/-! ## Upgrade to a unitary equivalence `L²(0,∞) ≃ L²(ℝ)` -/

/-- Change of variables `x = eᵗ` for lower Lebesgue integrals. -/
theorem lintegral_Ioi_eq_lintegral_exp_mul (g : ℝ → ENNReal) :
    ∫⁻ x in Ioi (0 : ℝ), g x = ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t) * g (Real.exp t) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
    (s := (univ : Set ℝ)) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g
  rw [image_univ, Real.range_exp] at h
  simpa only [Measure.restrict_univ, abs_of_pos (Real.exp_pos _)] using h

/-- `exp` pulls back null sets of `volume.restrict (Ioi 0)` to null sets of `volume`. -/
theorem quasiMeasurePreserving_exp :
    Measure.QuasiMeasurePreserving Real.exp volume (volume.restrict (Ioi (0 : ℝ))) := by
  refine ⟨Real.measurable_exp, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply Real.measurable_exp hs]
  have h1 : ∫⁻ x in Ioi (0 : ℝ), s.indicator 1 x = 0 := by
    rw [lintegral_indicator_one hs]; simpa using hs0
  rw [lintegral_Ioi_eq_lintegral_exp_mul] at h1
  have hmeas : Measurable fun t : ℝ =>
      ENNReal.ofReal (Real.exp t) * s.indicator (1 : ℝ → ENNReal) (Real.exp t) :=
    (ENNReal.measurable_ofReal.comp Real.measurable_exp).mul
      ((measurable_one.indicator hs).comp Real.measurable_exp)
  have h2 := (lintegral_eq_zero_iff hmeas).mp h1
  refine measure_eq_zero_iff_ae_notMem.mpr ?_
  filter_upwards [h2] with t ht hts
  have hts' : Real.exp t ∈ s := hts
  rw [Pi.zero_apply, Set.indicator_of_mem hts', Pi.one_apply, mul_one] at ht
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos t)).ne' ht

/-- `log` pulls back null sets of `volume` to null sets of `volume.restrict (Ioi 0)`. -/
theorem quasiMeasurePreserving_log :
    Measure.QuasiMeasurePreserving Real.log (volume.restrict (Ioi (0 : ℝ))) volume := by
  refine ⟨Real.measurable_log, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply Real.measurable_log hs, Measure.restrict_apply (Real.measurable_log hs)]
  have himg : Real.log ⁻¹' s ∩ Ioi 0 = Real.exp '' s := by
    ext x
    refine ⟨fun hx => ⟨Real.log x, hx.1, Real.exp_log hx.2⟩, ?_⟩
    rintro ⟨t, ht, rfl⟩
    exact ⟨by simpa only [Set.mem_preimage, Real.log_exp] using ht, Real.exp_pos t⟩
  rw [himg]
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
    (s := s) hs (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (Real.exp_injective.injOn.mono (subset_univ s)) (fun _ => 1)
  simp only [mul_one] at h
  rw [← setLIntegral_one, h, setLIntegral_measure_zero _ _ hs0]

/-- `U` preserves the `L²` norm, as an `eLpNorm` identity, with no hypothesis on `f`. -/
theorem eLpNorm_logSub (f : ℝ → F) :
    eLpNorm (logSub f) 2 volume = eLpNorm f 2 (volume.restrict (Ioi (0 : ℝ))) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    lintegral_Ioi_eq_lintegral_exp_mul (fun x => ‖f x‖ₑ ^ (2 : ENNReal).toReal)]
  congr 1
  refine lintegral_congr fun t => ?_
  rw [logSub, enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  congr 1
  rw [Real.enorm_eq_ofReal (Real.exp_pos _).le, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _)]
  congr 1
  rw [show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, ← Real.exp_mul]
  ring_nf

/-- `U⁻¹` preserves the `L²` norm. -/
theorem eLpNorm_logSubSymm (h : ℝ → F) :
    eLpNorm (logSubSymm h) 2 (volume.restrict (Ioi (0 : ℝ))) = eLpNorm h 2 volume := by
  rw [← eLpNorm_logSub (logSubSymm h), logSub_logSubSymm]

theorem aestronglyMeasurable_logSub {f : ℝ → F}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ)))) :
    AEStronglyMeasurable (logSub f) volume :=
  AEStronglyMeasurable.smul
    ((Real.continuous_exp.comp (continuous_id.div_const 2)).aestronglyMeasurable)
    (hf.comp_quasiMeasurePreserving quasiMeasurePreserving_exp)

theorem aestronglyMeasurable_logSubSymm {h : ℝ → F} (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (logSubSymm h) (volume.restrict (Ioi (0 : ℝ))) :=
  AEStronglyMeasurable.smul ((measurable_id.pow_const (-(1 : ℝ) / 2)).aestronglyMeasurable)
    (hh.comp_quasiMeasurePreserving quasiMeasurePreserving_log)

theorem memLp_logSub {f : ℝ → F} (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) :
    MemLp (logSub f) 2 volume :=
  ⟨aestronglyMeasurable_logSub hf.1, by rw [eLpNorm_logSub]; exact hf.2⟩

theorem memLp_logSubSymm {h : ℝ → F} (hh : MemLp h 2 volume) :
    MemLp (logSubSymm h) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  ⟨aestronglyMeasurable_logSubSymm hh.1, by rw [eLpNorm_logSubSymm]; exact hh.2⟩

theorem logSub_congr_ae {f g : ℝ → F} (hfg : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g) :
    logSub f =ᵐ[volume] logSub g := by
  filter_upwards [quasiMeasurePreserving_exp.ae_eq_comp hfg] with t ht
  simp only [logSub]
  rw [show f (Real.exp t) = (f ∘ Real.exp) t from rfl, ht]
  rfl

theorem logSubSymm_congr_ae {h k : ℝ → F} (hhk : h =ᵐ[volume] k) :
    logSubSymm h =ᵐ[volume.restrict (Ioi (0 : ℝ))] logSubSymm k := by
  filter_upwards [quasiMeasurePreserving_log.ae_eq_comp hhk] with x hx
  simp only [logSubSymm]
  rw [show h (Real.log x) = (h ∘ Real.log) x from rfl, hx]
  rfl

variable (F)
variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 F] [IsBoundedSMul 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The unitary `U : L²(0, ∞) ≃ L²(ℝ)` induced by the substitution `x = eᵗ`,
`(U f)(t) = e^{t/2} · f(eᵗ)`, with inverse `(U⁻¹ h)(x) = x^{-1/2} · h(log x)`. -/
noncomputable def mellinLogEquiv :
    Lp F 2 (volume.restrict (Ioi (0 : ℝ))) ≃ₗᵢ[𝕜] Lp F 2 (volume : Measure ℝ) :=
  LinearIsometryEquiv.mk
    { toFun := fun f => MemLp.toLp (logSub (f : ℝ → F)) (memLp_logSub (Lp.memLp f))
      map_add' := by
        intro f g
        refine Lp.ext ?_
        refine ((MemLp.coeFn_toLp _).trans ?_).trans (Lp.coeFn_add _ _).symm
        refine (logSub_congr_ae (Lp.coeFn_add f g)).trans ?_
        filter_upwards [MemLp.coeFn_toLp (memLp_logSub (Lp.memLp f)),
          MemLp.coeFn_toLp (memLp_logSub (Lp.memLp g))] with t h1 h2
        simp only [logSub, Pi.add_apply, smul_add, h1, h2]
      map_smul' := by
        intro c f
        refine Lp.ext ?_
        refine ((MemLp.coeFn_toLp _).trans ?_).trans (Lp.coeFn_smul _ _).symm
        refine (logSub_congr_ae (Lp.coeFn_smul c f)).trans ?_
        filter_upwards [MemLp.coeFn_toLp (memLp_logSub (Lp.memLp f))] with t h1
        simp only [logSub, Pi.smul_apply, h1, RingHom.id_apply, smul_comm]
      invFun := fun h => MemLp.toLp (logSubSymm (h : ℝ → F)) (memLp_logSubSymm (Lp.memLp h))
      left_inv := by
        intro f
        refine Lp.ext ?_
        refine (MemLp.coeFn_toLp _).trans ?_
        refine (logSubSymm_congr_ae (MemLp.coeFn_toLp (memLp_logSub (Lp.memLp f)))).trans ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact logSubSymm_logSub _ hx
      right_inv := by
        intro h
        refine Lp.ext ?_
        refine (MemLp.coeFn_toLp _).trans ?_
        refine (logSub_congr_ae (MemLp.coeFn_toLp (memLp_logSubSymm (Lp.memLp h)))).trans ?_
        rw [logSub_logSubSymm] }
    (by
      intro f
      simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_def]
      rw [eLpNorm_congr_ae (MemLp.coeFn_toLp _), eLpNorm_logSub])

@[simp]
theorem coeFn_mellinLogEquiv (f : Lp F 2 (volume.restrict (Ioi (0 : ℝ)))) :
    (mellinLogEquiv F (𝕜 := 𝕜) f : ℝ → F) =ᵐ[volume] logSub (f : ℝ → F) :=
  MemLp.coeFn_toLp (memLp_logSub (Lp.memLp f))

@[simp]
theorem coeFn_mellinLogEquiv_symm (h : Lp F 2 (volume : Measure ℝ)) :
    ((mellinLogEquiv F (𝕜 := 𝕜)).symm h : ℝ → F)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] logSubSymm (h : ℝ → F) :=
  MemLp.coeFn_toLp (memLp_logSubSymm (Lp.memLp h))

/-- The scalar (complex-valued) case: the substitution `x = eᵗ` is a unitary, i.e. a `ℂ`-linear
isometry equivalence, `L²((0, ∞), ℂ) ≃ L²(ℝ, ℂ)`. -/
noncomputable def mellinLogUnitaryComplex :
    Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  mellinLogEquiv ℂ (𝕜 := ℂ)

end DilationGenerator
end Brockian

