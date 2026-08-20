import Mathlib

/-!
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The substitution `x = exp t` as an identity of Lebesgue (`ℝ≥0∞`-valued) integrals:
integrating over `(0, ∞)` is the same as integrating `exp t • ·` over all of `ℝ`. -/
theorem lintegral_Ioi_eq_lintegral_exp_smul (g : ℝ → ENNReal) :
    ∫⁻ x in Ioi (0 : ℝ), g x = ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t) * g (Real.exp t) := by
  have himg : Real.exp '' (univ : Set ℝ) = Ioi (0 : ℝ) := by
    simp [Set.image_univ, Real.range_exp]
  have h :=
    MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
      (s := (univ : Set ℝ)) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (Real.exp_injective.injOn) g
  rw [himg, Measure.restrict_univ] at h
  simpa [abs_of_pos (Real.exp_pos _)] using h

/-- The substitution `x = exp t` as an identity of Bochner integrals: for any function
`g : ℝ → E`, the integral of `g` over `(0, ∞)` equals the integral of `t ↦ exp t • g (exp t)`
over `ℝ`.  No integrability hypotheses are needed: if one side fails to be integrable, so does
the other, and both integrals are then `0`. -/
theorem integral_Ioi_eq_integral_exp_smul (g : ℝ → E) :
    ∫ x in Ioi (0 : ℝ), g x = ∫ t : ℝ, Real.exp t • g (Real.exp t) := by
  have himg : Real.exp '' (univ : Set ℝ) = Ioi (0 : ℝ) := by
    simp [Set.image_univ, Real.range_exp]
  have h :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul (f := Real.exp) (f' := Real.exp)
      (s := (univ : Set ℝ)) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (Real.exp_injective.injOn) g
  rw [himg, Measure.restrict_univ] at h
  simpa [abs_of_pos (Real.exp_pos _)] using h

/-- **Mellin log unitary (norm preservation).**
The substitution `x = e^t` turns `L²(0, ∞)` into `L²(ℝ)` via
`(U f)(t) = e^{t/2} • f (e^t)`; this map preserves the `L²` integral. -/
theorem mellin_log_unitary (f : ℝ → E) :
    ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 = ∫ t : ℝ, ‖Real.exp (t / 2) • f (Real.exp t)‖ ^ 2 := by
  rw [integral_Ioi_eq_integral_exp_smul (E := ℝ) (fun x => ‖f x‖ ^ 2)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hsq : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [sq, ← Real.exp_add]
    ring_nf
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, hsq, smul_eq_mul]

/-- The pointwise inverse of the substitution: applying `h ↦ (x ↦ x^{-1/2} • h (log x))` to
`U f` recovers `f` on `(0, ∞)`. -/
theorem inverse_left_inv (f : ℝ → E) {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 : ℝ) / 2) •
        (Real.exp (Real.log x / 2) • f (Real.exp (Real.log x))) = f x := by
  rw [Real.exp_log hx]
  have hlog : Real.exp (Real.log x / 2) = x ^ ((1 : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos hx]
    ring_nf
  rw [hlog, smul_smul, ← Real.rpow_add hx]
  norm_num

/-- The pointwise inverse of the substitution, in the other direction: applying
`f ↦ (t ↦ e^{t/2} • f (e^t))` to `x ↦ x^{-1/2} • h (log x)` recovers `h`. -/
theorem inverse_right_inv (h : ℝ → E) (t : ℝ) :
    Real.exp (t / 2) •
        ((Real.exp t) ^ (-(1 : ℝ) / 2) • h (Real.log (Real.exp t))) = h t := by
  rw [Real.log_exp, smul_smul, Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp,
    ← Real.exp_add]
  have hz : t / 2 + t * (-(1 : ℝ) / 2) = 0 := by ring
  rw [hz, Real.exp_zero, one_smul]


/-! ### Measure-theoretic form of the substitution -/

/-- The density `e^t` appearing in the change of variables `x = e^t`. -/
noncomputable def expDensity : ℝ → ENNReal := fun t => ENNReal.ofReal (Real.exp t)

lemma measurable_expDensity : Measurable expDensity :=
  ENNReal.measurable_ofReal.comp Real.measurable_exp

lemma volume_image_exp {s : Set ℝ} (hs : MeasurableSet s) :
    volume (Real.exp '' s) = ∫⁻ t in s, expDensity t := by
  have h :=
    MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
      hs (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) (Real.exp_injective.injOn)
      (fun _ => 1)
  simpa [expDensity, abs_of_pos (Real.exp_pos _), MeasureTheory.lintegral_one,
    Measure.restrict_apply_univ] using h

lemma log_preimage_inter_Ioi (A : Set ℝ) :
    Real.log ⁻¹' A ∩ Ioi (0 : ℝ) = Real.exp '' A := by
  ext x
  constructor
  · rintro ⟨hxA, hx⟩
    exact ⟨Real.log x, hxA, Real.exp_log hx⟩
  · rintro ⟨t, htA, rfl⟩
    exact ⟨by simpa [Real.log_exp] using htA, Real.exp_pos t⟩

/-- `exp` sends the measure `e^t dt` on `ℝ` to Lebesgue measure on `(0, ∞)`. -/
lemma measurePreserving_exp :
    MeasurePreserving Real.exp (volume.withDensity expDensity)
      (volume.restrict (Ioi (0 : ℝ))) := by
  refine ⟨Real.measurable_exp, ?_⟩
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply Real.measurable_exp hA, Measure.restrict_apply hA,
    withDensity_apply _ (hA.preimage Real.measurable_exp)]
  have himg : Real.exp '' (Real.exp ⁻¹' A) = A ∩ Ioi (0 : ℝ) := by
    rw [Set.image_preimage_eq_inter_range, Real.range_exp]
  rw [← himg, volume_image_exp (hA.preimage Real.measurable_exp)]

/-- `log` sends Lebesgue measure on `(0, ∞)` to the measure `e^t dt` on `ℝ`. -/
lemma measurePreserving_log :
    MeasurePreserving Real.log (volume.restrict (Ioi (0 : ℝ)))
      (volume.withDensity expDensity) := by
  refine ⟨Real.measurable_log, ?_⟩
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply Real.measurable_log hA,
    Measure.restrict_apply (hA.preimage Real.measurable_log), withDensity_apply _ hA,
    ← volume_image_exp hA, log_preimage_inter_Ioi]

lemma volume_absolutelyContinuous_withDensity_exp :
    (volume : Measure ℝ) ≪ volume.withDensity expDensity := by
  have hmul : (expDensity * fun t => ENNReal.ofReal (Real.exp (-t))) = 1 := by
    funext t
    simp [expDensity, ← ENNReal.ofReal_mul (Real.exp_pos t).le, ← Real.exp_add]
  have h : (volume : Measure ℝ)
      = (volume.withDensity expDensity).withDensity fun t => ENNReal.ofReal (Real.exp (-t)) := by
    have hg : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-t)) := by fun_prop
    rw [← withDensity_mul _ measurable_expDensity hg, hmul, withDensity_one]
  conv_lhs => rw [h]
  exact withDensity_absolutelyContinuous _ _


/-! ### The maps `U` and `U⁻¹` at the level of functions -/

/-- `U f (t) = e^{t/2} • f (e^t)`. -/
noncomputable def mellinLog (f : ℝ → E) : ℝ → E := fun t => Real.exp (t / 2) • f (Real.exp t)

/-- `U⁻¹ h (x) = x^{-1/2} • h (log x)`. -/
noncomputable def mellinLogSymm (h : ℝ → E) : ℝ → E :=
  fun x => x ^ (-(1 : ℝ) / 2) • h (Real.log x)

@[simp] lemma mellinLog_mellinLogSymm (h : ℝ → E) : mellinLog (mellinLogSymm h) = h := by
  funext t
  simpa [mellinLog, mellinLogSymm] using inverse_right_inv h t

lemma mellinLogSymm_mellinLog_apply (f : ℝ → E) {x : ℝ} (hx : 0 < x) :
    mellinLogSymm (mellinLog f) x = f x := by
  simpa [mellinLog, mellinLogSymm] using inverse_left_inv f hx

lemma mellinLogSymm_mellinLog_ae (f : ℝ → E) :
    mellinLogSymm (mellinLog f) =ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
  exact mellinLogSymm_mellinLog_apply f hx

/-! ### `L²` norm preservation -/

lemma lintegral_enorm_rpow_mellinLog (f : ℝ → E) :
    ∫⁻ t : ℝ, ‖mellinLog f t‖ₑ ^ (2 : ℝ)
      = ∫⁻ x in Ioi (0 : ℝ), ‖f x‖ₑ ^ (2 : ℝ) := by
  rw [lintegral_Ioi_eq_lintegral_exp_smul (fun x => ‖f x‖ₑ ^ (2 : ℝ))]
  refine lintegral_congr fun t => ?_
  have hpos : (0 : ℝ) < Real.exp (t / 2) := Real.exp_pos _
  have hsq : Real.exp (t / 2) ^ (2 : ℝ) = Real.exp t := by
    rw [Real.rpow_def_of_pos hpos, Real.log_exp]
    ring_nf
  rw [mellinLog, enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
    Real.enorm_eq_ofReal hpos.le, ENNReal.ofReal_rpow_of_pos hpos, hsq]

lemma eLpNorm_mellinLog (f : ℝ → E) :
    eLpNorm (mellinLog f) 2 volume = eLpNorm f 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have htwo : (2 : ENNReal).toReal = (2 : ℝ) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), htwo,
    lintegral_enorm_rpow_mellinLog f]

lemma eLpNorm_mellinLogSymm (h : ℝ → E) :
    eLpNorm (mellinLogSymm h) 2 (volume.restrict (Ioi (0 : ℝ))) = eLpNorm h 2 volume := by
  have := eLpNorm_mellinLog (mellinLogSymm h)
  rwa [mellinLog_mellinLogSymm, eq_comm] at this

/-! ### Measurability transfer -/

lemma aestronglyMeasurable_mellinLog {f : ℝ → E}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ)))) :
    AEStronglyMeasurable (mellinLog f) volume := by
  have h1 : AEStronglyMeasurable (f ∘ Real.exp) (volume.withDensity expDensity) :=
    hf.comp_measurePreserving measurePreserving_exp
  have h2 : AEStronglyMeasurable (f ∘ Real.exp) volume :=
    h1.mono_ac volume_absolutelyContinuous_withDensity_exp
  have h3 : AEStronglyMeasurable (fun t : ℝ => Real.exp (t / 2)) volume :=
    (Real.continuous_exp.comp (continuous_id.div_const 2)).aestronglyMeasurable
  exact h3.smul h2

lemma aestronglyMeasurable_mellinLogSymm {h : ℝ → E} (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (mellinLogSymm h) (volume.restrict (Ioi (0 : ℝ))) := by
  have h1 : AEStronglyMeasurable h (volume.withDensity expDensity) :=
    hh.mono_ac (withDensity_absolutelyContinuous _ _)
  have h2 : AEStronglyMeasurable (h ∘ Real.log) (volume.restrict (Ioi (0 : ℝ))) :=
    h1.comp_measurePreserving measurePreserving_log
  have h3 : AEStronglyMeasurable (fun x : ℝ => x ^ (-(1 : ℝ) / 2))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (Measurable.pow_const (f := fun x : ℝ => x) measurable_id _).aestronglyMeasurable
  exact h3.smul h2

lemma memLp_mellinLog {f : ℝ → E} (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) :
    MemLp (mellinLog f) 2 volume :=
  ⟨aestronglyMeasurable_mellinLog hf.1, by rw [eLpNorm_mellinLog]; exact hf.2⟩

lemma memLp_mellinLogSymm {h : ℝ → E} (hh : MemLp h 2 volume) :
    MemLp (mellinLogSymm h) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  ⟨aestronglyMeasurable_mellinLogSymm hh.1, by rw [eLpNorm_mellinLogSymm]; exact hh.2⟩


/-! ### Compatibility with a.e. equality and with the linear structure -/

lemma mellinLog_congr_ae {f g : ℝ → E} (h : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g) :
    mellinLog f =ᵐ[volume] mellinLog g := by
  have h1 : (f ∘ Real.exp) =ᵐ[volume.withDensity expDensity] (g ∘ Real.exp) :=
    measurePreserving_exp.quasiMeasurePreserving.ae_eq_comp h
  have h2 : (f ∘ Real.exp) =ᵐ[volume] (g ∘ Real.exp) :=
    h1.filter_mono volume_absolutelyContinuous_withDensity_exp.ae_le
  filter_upwards [h2] with t ht
  simp only [mellinLog, Function.comp_apply] at ht ⊢
  rw [ht]

lemma mellinLogSymm_congr_ae {h₁ h₂ : ℝ → E} (h : h₁ =ᵐ[volume] h₂) :
    mellinLogSymm h₁ =ᵐ[volume.restrict (Ioi (0 : ℝ))] mellinLogSymm h₂ := by
  have h1 : h₁ =ᵐ[volume.withDensity expDensity] h₂ :=
    h.filter_mono (withDensity_absolutelyContinuous (volume : Measure ℝ) expDensity).ae_le
  have h2 : (h₁ ∘ Real.log) =ᵐ[volume.restrict (Ioi (0 : ℝ))] (h₂ ∘ Real.log) :=
    measurePreserving_log.quasiMeasurePreserving.ae_eq_comp h1
  filter_upwards [h2] with x hx
  simp only [mellinLogSymm, Function.comp_apply] at hx ⊢
  rw [hx]

lemma mellinLog_add (f g : ℝ → E) : mellinLog (f + g) = mellinLog f + mellinLog g := by
  funext t
  simp [mellinLog, smul_add]

lemma mellinLog_smul (c : ℝ) (f : ℝ → E) : mellinLog (c • f) = c • mellinLog f := by
  funext t
  show Real.exp (t / 2) • (c • f (Real.exp t)) = c • (Real.exp (t / 2) • f (Real.exp t))
  rw [smul_comm]

/-! ### The unitary `U : L²(0, ∞) ≃ L²(ℝ)` -/

/-- The map `U f = (t ↦ e^{t/2} • f (e^t))` at the level of `L²` spaces. -/
noncomputable def toLpFun (f : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) : Lp E 2 (volume : Measure ℝ) :=
  (memLp_mellinLog (Lp.memLp f)).toLp _

/-- The map `U⁻¹ h = (x ↦ x^{-1/2} • h (log x))` at the level of `L²` spaces. -/
noncomputable def ofLpFun (h : Lp E 2 (volume : Measure ℝ)) : Lp E 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (memLp_mellinLogSymm (Lp.memLp h)).toLp _

lemma coeFn_toLpFun (f : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) :
    ⇑(toLpFun f) =ᵐ[volume] mellinLog ⇑f :=
  MemLp.coeFn_toLp _

lemma coeFn_ofLpFun (h : Lp E 2 (volume : Measure ℝ)) :
    ⇑(ofLpFun h) =ᵐ[volume.restrict (Ioi (0 : ℝ))] mellinLogSymm ⇑h :=
  MemLp.coeFn_toLp _

lemma toLpFun_add (f g : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) :
    toLpFun (f + g) = toLpFun f + toLpFun g := by
  refine Lp.ext_iff.2 ?_
  filter_upwards [coeFn_toLpFun (f + g), coeFn_toLpFun f, coeFn_toLpFun g,
    Lp.coeFn_add (toLpFun f) (toLpFun g), mellinLog_congr_ae (Lp.coeFn_add f g)]
    with t h1 h2 h3 h4 h5
  rw [h1, h4, h5, mellinLog_add]
  simp [h2, h3]

lemma toLpFun_smul (c : ℝ) (f : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) :
    toLpFun (c • f) = c • toLpFun f := by
  refine Lp.ext_iff.2 ?_
  filter_upwards [coeFn_toLpFun (c • f), coeFn_toLpFun f, Lp.coeFn_smul c (toLpFun f),
    mellinLog_congr_ae (Lp.coeFn_smul c f)] with t h1 h2 h3 h4
  rw [h1, h3, h4, mellinLog_smul]
  simp [h2]

lemma ofLpFun_toLpFun (f : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) :
    ofLpFun (toLpFun f) = f := by
  refine Lp.ext_iff.2 ?_
  filter_upwards [coeFn_ofLpFun (toLpFun f), mellinLogSymm_congr_ae (coeFn_toLpFun f),
    mellinLogSymm_mellinLog_ae (⇑f)] with x h1 h2 h3
  rw [h1, h2, h3]

lemma toLpFun_ofLpFun (h : Lp E 2 (volume : Measure ℝ)) : toLpFun (ofLpFun h) = h := by
  refine Lp.ext_iff.2 ?_
  filter_upwards [coeFn_toLpFun (ofLpFun h), mellinLog_congr_ae (coeFn_ofLpFun h)] with t h1 h2
  rw [h1, h2, mellinLog_mellinLogSymm]

lemma norm_toLpFun (f : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) : ‖toLpFun f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (coeFn_toLpFun f), eLpNorm_mellinLog]

/-- **The Mellin logarithmic substitution as a unitary.**
The substitution `x = e^t` induces a surjective linear isometry
`U : L²(0, ∞) ≃ L²(ℝ)`, `(U f)(t) = e^{t/2} • f (e^t)`, with inverse
`(U⁻¹ h)(x) = x^{-1/2} • h (log x)`. -/
noncomputable def mellinLogUnitary :
    Lp E 2 (volume.restrict (Ioi (0 : ℝ))) ≃ₗᵢ[ℝ] Lp E 2 (volume : Measure ℝ) where
  toFun := toLpFun
  map_add' := toLpFun_add
  map_smul' := toLpFun_smul
  invFun := ofLpFun
  left_inv := ofLpFun_toLpFun
  right_inv := toLpFun_ofLpFun
  norm_map' := norm_toLpFun

@[simp] lemma mellinLogUnitary_apply (f : Lp E 2 (volume.restrict (Ioi (0 : ℝ)))) :
    (mellinLogUnitary f : ℝ → E) =ᵐ[volume] mellinLog ⇑f :=
  coeFn_toLpFun f

@[simp] lemma mellinLogUnitary_symm_apply (h : Lp E 2 (volume : Measure ℝ)) :
    ((mellinLogUnitary (E := E)).symm h : ℝ → E)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] mellinLogSymm ⇑h :=
  coeFn_ofLpFun h

end DilationGenerator
end Brockian

