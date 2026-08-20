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

import Mathlib

/-!
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Set Real
open scoped ENNReal NNReal

namespace Brockian.DilationGenerator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The substitution `x = exp t` maps `ℝ` onto `(0, ∞)`. -/
lemma exp_image_univ : Real.exp '' (univ : Set ℝ) = Ioi (0 : ℝ) := by
  rw [Set.image_univ, Real.range_exp]

/-- Change of variables `x = exp t` for lower Lebesgue integrals. -/
lemma lintegral_Ioi_comp_exp (g : ℝ → ℝ≥0∞) :
    ∫⁻ x in Ioi (0 : ℝ), g x = ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t) * g (Real.exp t) := by
  have h := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp)
    (f' := Real.exp) (s := univ) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (Real.exp_injective.injOn) g
  rw [exp_image_univ] at h
  simpa [abs_of_pos (Real.exp_pos _), Measure.restrict_univ] using h

/-- Change of variables `x = exp t` for Bochner integrals over `(0, ∞)`. -/
lemma integral_Ioi_comp_exp (g : ℝ → E) :
    ∫ x in Ioi (0 : ℝ), g x = ∫ t : ℝ, Real.exp t • g (Real.exp t) := by
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (f := Real.exp)
    (f' := Real.exp) (s := univ) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (Real.exp_injective.injOn) g
  rw [exp_image_univ] at h
  simpa [abs_of_pos (Real.exp_pos _), Measure.restrict_univ] using h

/-- The forward map of the Mellin/logarithmic substitution:
`(U f)(t) = e^{t/2} · f (e^t)`. -/
noncomputable def toLog (f : ℝ → E) : ℝ → E := fun t => Real.exp (t / 2) • f (Real.exp t)

/-- The inverse map of the Mellin/logarithmic substitution:
`(U⁻¹ h)(x) = x^{-1/2} · h (log x)`. -/
noncomputable def ofLog (h : ℝ → E) : ℝ → E := fun x => (x ^ (-(1 : ℝ) / 2) : ℝ) • h (Real.log x)

lemma toLog_apply (f : ℝ → E) (t : ℝ) : toLog f t = Real.exp (t / 2) • f (Real.exp t) := rfl

lemma ofLog_apply (h : ℝ → E) (x : ℝ) :
    ofLog h x = (x ^ (-(1 : ℝ) / 2) : ℝ) • h (Real.log x) := rfl

/-- `ofLog` is a left inverse of `toLog` on `(0, ∞)`. -/
lemma ofLog_toLog (f : ℝ → E) {x : ℝ} (hx : 0 < x) : ofLog (toLog f) x = f x := by
  have hlog : Real.exp (Real.log x) = x := Real.exp_log hx
  rw [ofLog_apply, toLog_apply, hlog, smul_smul]
  have hkey : (x ^ (-(1 : ℝ) / 2) : ℝ) * Real.exp (Real.log x / 2) = 1 := by
    rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
    rw [show Real.log x * (-(1 : ℝ) / 2) + Real.log x / 2 = 0 by ring, Real.exp_zero]
  rw [hkey, one_smul]

/-- `ofLog` is a right inverse of `toLog`. -/
lemma toLog_ofLog (h : ℝ → E) (t : ℝ) : toLog (ofLog h) t = h t := by
  rw [toLog_apply, ofLog_apply, Real.log_exp, smul_smul]
  have hkey : Real.exp (t / 2) * ((Real.exp t) ^ (-(1 : ℝ) / 2) : ℝ) = 1 := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
    rw [show t / 2 + t * (-(1 : ℝ) / 2) = 0 by ring, Real.exp_zero]
  rw [hkey, one_smul]

/-- `toLog` is linear. -/
lemma toLog_add (f g : ℝ → E) : toLog (f + g) = toLog f + toLog g := by
  funext t; simp [toLog_apply, smul_add]

lemma toLog_smul (c : ℝ) (f : ℝ → E) : toLog (c • f) = c • toLog f := by
  funext t
  show Real.exp (t / 2) • (c • f (Real.exp t)) = c • Real.exp (t / 2) • f (Real.exp t)
  rw [smul_comm]

/-- `e^{t/2}` squared is `e^t`. -/
lemma exp_half_sq (t : ℝ) : Real.exp (t / 2) ^ 2 = Real.exp t := by
  rw [sq, ← Real.exp_add, add_halves]

/-- **Mellin log unitary (L²-norm preservation).**
The substitution `x = e^t`, together with the weight `e^{t/2}`, preserves the `L²` integral:
`∫_{(0,∞)} ‖f x‖² dx = ∫_ℝ ‖e^{t/2} f(e^t)‖² dt`. -/
theorem mellin_log_unitary (f : ℝ → E) :
    ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 = ∫ t : ℝ, ‖Real.exp (t / 2) • f (Real.exp t)‖ ^ 2 := by
  rw [integral_Ioi_comp_exp (fun x => ‖f x‖ ^ 2)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), smul_eq_mul, mul_pow,
    exp_half_sq]

/-- Restated in terms of `toLog`. -/
theorem mellin_log_unitary' (f : ℝ → E) :
    ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 = ∫ t : ℝ, ‖toLog f t‖ ^ 2 :=
  mellin_log_unitary f

/-- **The `L²` (indeed `L^p`) norm is preserved, at the level of `eLpNorm`.**
This is the unitarity statement without any integrability assumption on `f`. -/
theorem eLpNorm_toLog (f : ℝ → E) :
    eLpNorm (toLog f) 2 volume = eLpNorm f 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hpt : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  congr 1
  rw [lintegral_Ioi_comp_exp (fun x => ‖f x‖ₑ ^ ((2 : ℝ≥0∞).toReal))]
  refine lintegral_congr fun t => ?_
  rw [toLog_apply, enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  congr 1
  rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]
  simp only [ENNReal.toReal_ofNat]
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
  norm_num

/-- The corresponding statement for the inverse map `ofLog`. -/
theorem eLpNorm_ofLog (h : ℝ → E) :
    eLpNorm (ofLog h) 2 (volume.restrict (Ioi (0 : ℝ))) = eLpNorm h 2 volume := by
  rw [← eLpNorm_toLog (ofLog h)]
  congr 1
  exact funext (toLog_ofLog h)

/-! ### Transfer of measurability -/

/-- `exp` is quasi measure preserving from Lebesgue measure on `ℝ` to Lebesgue measure
on `(0, ∞)`. -/
lemma exp_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving Real.exp volume (volume.restrict (Ioi (0 : ℝ))) := by
  refine ⟨Real.measurable_exp, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply Real.measurable_exp hs]
  have h := lintegral_Ioi_comp_exp (s.indicator 1)
  rw [lintegral_indicator_one hs, hs0] at h
  have hmeas : Measurable
      (fun t : ℝ => ENNReal.ofReal (Real.exp t) * s.indicator 1 (Real.exp t)) :=
    (ENNReal.measurable_ofReal.comp Real.measurable_exp).mul
      ((measurable_one.indicator hs).comp Real.measurable_exp)
  have h0 := (lintegral_eq_zero_iff hmeas).1 h.symm
  have key : (Real.exp ⁻¹' s).indicator (1 : ℝ → ℝ≥0∞) =ᵐ[volume] 0 := by
    filter_upwards [h0] with t ht
    simp only [Pi.zero_apply, mul_eq_zero] at ht ⊢
    rcases ht with h1 | h2
    · exact absurd h1 (by simp [Real.exp_pos t])
    · simpa [Set.indicator_apply] using h2
  rw [← lintegral_indicator_one (Real.measurable_exp hs)]
  exact (lintegral_congr_ae key).trans (by simp)

/-- `log` is quasi measure preserving from Lebesgue measure on `(0, ∞)` to Lebesgue measure
on `ℝ`. -/
lemma log_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving Real.log (volume.restrict (Ioi (0 : ℝ))) volume := by
  refine ⟨Real.measurable_log, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply Real.measurable_log hs, ← lintegral_indicator_one (Real.measurable_log hs),
    lintegral_Ioi_comp_exp]
  have key : ∀ᵐ t : ℝ,
      ENNReal.ofReal (Real.exp t) * (Real.log ⁻¹' s).indicator 1 (Real.exp t) = 0 := by
    have hs' : s.indicator (1 : ℝ → ℝ≥0∞) =ᵐ[volume] 0 := by
      rw [Filter.EventuallyEq, ae_iff]
      simp only [Pi.zero_apply, Set.indicator_apply_eq_zero, Pi.one_apply, one_ne_zero,
        imp_false, not_not]
      simpa using hs0
    filter_upwards [hs'] with t ht
    by_cases h : t ∈ s
    · simp [h] at ht
    · simp [h]
  rw [lintegral_congr_ae key]
  simp

lemma toLog_congr_ae {f g : ℝ → E} (h : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g) :
    toLog f =ᵐ[volume] toLog g := by
  filter_upwards [exp_quasiMeasurePreserving.ae h] with t ht
  simp only [toLog_apply, ht]

lemma ofLog_congr_ae {f g : ℝ → E} (h : f =ᵐ[volume] g) :
    ofLog f =ᵐ[volume.restrict (Ioi (0 : ℝ))] ofLog g := by
  filter_upwards [log_quasiMeasurePreserving.ae h] with x hx
  simp only [ofLog_apply, hx]

lemma aestronglyMeasurable_toLog {f : ℝ → E}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ)))) :
    AEStronglyMeasurable (toLog f) volume := by
  have h1 : AEStronglyMeasurable (fun t : ℝ => f (Real.exp t)) volume :=
    hf.comp_quasiMeasurePreserving exp_quasiMeasurePreserving
  have h2 : Continuous fun t : ℝ => Real.exp (t / 2) :=
    Real.continuous_exp.comp (continuous_id.div_const 2)
  exact h2.aestronglyMeasurable.smul h1

lemma aestronglyMeasurable_ofLog {h : ℝ → E} (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (ofLog h) (volume.restrict (Ioi (0 : ℝ))) := by
  have h1 : AEStronglyMeasurable (fun x : ℝ => h (Real.log x))
      (volume.restrict (Ioi (0 : ℝ))) :=
    hh.comp_quasiMeasurePreserving log_quasiMeasurePreserving
  have h2 : Measurable fun x : ℝ => (x ^ (-(1 : ℝ) / 2) : ℝ) := by fun_prop
  exact h2.aestronglyMeasurable.smul h1

/-- The substitution preserves membership in `L²`. -/
theorem memLp_toLog {f : ℝ → E} (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) :
    MemLp (toLog f) 2 volume :=
  ⟨aestronglyMeasurable_toLog hf.1, by rw [eLpNorm_toLog]; exact hf.2⟩

/-- The inverse substitution preserves membership in `L²`. -/
theorem memLp_ofLog {h : ℝ → E} (hh : MemLp h 2 volume) :
    MemLp (ofLog h) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  ⟨aestronglyMeasurable_ofLog hh.1, by rw [eLpNorm_ofLog]; exact hh.2⟩

/-! ### The unitary `L²(0, ∞) ≃ L²(ℝ)` -/

/-- The image in `L²(ℝ)` of an element of `L²(0, ∞)` under `f ↦ (t ↦ e^{t/2} f(e^t))`. -/
noncomputable def toLogLp (F : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) :
    Lp E 2 (volume : Measure ℝ) :=
  (memLp_toLog (Lp.memLp F)).toLp _

lemma coeFn_toLogLp (F : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) :
    (toLogLp F : ℝ → E) =ᵐ[volume] toLog (F : ℝ → E) := MemLp.coeFn_toLp _

/-- The image in `L²(0, ∞)` of an element of `L²(ℝ)` under `h ↦ (x ↦ x^{-1/2} h(log x))`. -/
noncomputable def ofLogLp (H : Lp E 2 (volume : Measure ℝ)) :
    Lp E 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (memLp_ofLog (Lp.memLp H)).toLp _

lemma coeFn_ofLogLp (H : Lp E 2 (volume : Measure ℝ)) :
    (ofLogLp H : ℝ → E) =ᵐ[volume.restrict (Ioi (0 : ℝ))] ofLog (H : ℝ → E) :=
  MemLp.coeFn_toLp _

lemma ofLogLp_toLogLp (F : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) :
    ofLogLp (toLogLp F) = F := by
  refine Lp.ext_iff.2 (((coeFn_ofLogLp _).trans (ofLog_congr_ae (coeFn_toLogLp F))).trans ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact ofLog_toLog _ hx

lemma toLogLp_ofLogLp (H : Lp E 2 (volume : Measure ℝ)) :
    toLogLp (ofLogLp H) = H := by
  refine Lp.ext_iff.2 (((coeFn_toLogLp _).trans (toLog_congr_ae (coeFn_ofLogLp H))).trans ?_)
  exact Filter.Eventually.of_forall (toLog_ofLog _)

lemma toLogLp_add (F G : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) :
    toLogLp (F + G) = toLogLp F + toLogLp G := by
  refine Lp.ext_iff.2 ?_
  have h1 : (toLogLp (F + G) : ℝ → E) =ᵐ[volume] toLog ((F : ℝ → E) + (G : ℝ → E)) :=
    (coeFn_toLogLp _).trans (toLog_congr_ae (Lp.coeFn_add F G))
  have h2 : ((toLogLp F + toLogLp G : Lp E 2 (volume : Measure ℝ)) : ℝ → E)
      =ᵐ[volume] toLog (F : ℝ → E) + toLog (G : ℝ → E) :=
    (Lp.coeFn_add _ _).trans ((coeFn_toLogLp F).add (coeFn_toLogLp G))
  rw [toLog_add] at h1
  exact h1.trans h2.symm

lemma toLogLp_smul (c : ℝ) (F : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) :
    toLogLp (c • F) = c • toLogLp F := by
  refine Lp.ext_iff.2 ?_
  have h1 : (toLogLp (c • F) : ℝ → E) =ᵐ[volume] toLog (c • (F : ℝ → E)) :=
    (coeFn_toLogLp _).trans (toLog_congr_ae (Lp.coeFn_smul c F))
  have h2 : ((c • toLogLp F : Lp E 2 (volume : Measure ℝ)) : ℝ → E)
      =ᵐ[volume] c • toLog (F : ℝ → E) :=
    (Lp.coeFn_smul _ _).trans ((coeFn_toLogLp F).const_smul c)
  rw [toLog_smul] at h1
  exact h1.trans h2.symm

lemma norm_toLogLp (F : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) : ‖toLogLp F‖ = ‖F‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_toLogLp F), eLpNorm_toLog]

/-- **The Mellin logarithmic substitution is unitary.**
The map `f ↦ (t ↦ e^{t/2} f(e^t))` is a linear isometric equivalence from `L²(0, ∞)` onto
`L²(ℝ)`, with inverse `h ↦ (x ↦ x^{-1/2} h (log x))`. -/
noncomputable def mellinLogEquiv :
    Lp E 2 (volume.restrict (Ioi (0 : ℝ))) ≃ₗᵢ[ℝ] Lp E 2 (volume : Measure ℝ) where
  toFun := toLogLp
  map_add' := toLogLp_add
  map_smul' := toLogLp_smul
  invFun := ofLogLp
  left_inv := ofLogLp_toLogLp
  right_inv := toLogLp_ofLogLp
  norm_map' := norm_toLogLp

@[simp] lemma mellinLogEquiv_apply (F : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) :
    (mellinLogEquiv F : Lp E 2 (volume : Measure ℝ)) = toLogLp F := rfl

@[simp] lemma mellinLogEquiv_symm_apply (H : Lp E 2 (volume : Measure ℝ)) :
    (mellinLogEquiv.symm H : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) = ofLogLp H := rfl

end Brockian.DilationGenerator

