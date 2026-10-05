/-
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The substitution `x = eᵗ` induces the *Mellin logarithmic change of variables*

`(U f)(t) = e^{t/2} • f (eᵗ)`,  `(U⁻¹ h)(x) = x^{-1/2} • h (log x)`,

which is a unitary `L²(0, ∞) ≃ L²(ℝ)`.  This file proves:

* `Brockian.DilationGenerator.map_exp_withDensity_exp`: the pushforward of
  `e^t dt` under `exp` is Lebesgue measure on `(0, ∞)` (the underlying
  change-of-variables statement, from `map_withDensity_abs_det_fderiv_eq_addHaar`);
* `Brockian.DilationGenerator.measurePreserving_exp`: the same fact phrased as
  `MeasurePreserving`;
* `Brockian.DilationGenerator.lintegral_Ioi_eq_lintegral_exp`: the change of
  variables for `ℝ≥0∞`-valued integrands (no hypotheses on the integrand);
* `Brockian.DilationGenerator.mellin_log_unitary`: **the target** — the map
  `U` preserves the `L²` integral, for an arbitrary `f : ℝ → E`;
* `Brockian.DilationGenerator.eLpNorm_mellinLog`: the `L²` seminorm identity
  `eLpNorm (U f) 2 volume = eLpNorm f 2 (volume.restrict (Ioi 0))` in `ℝ≥0∞`,
  again with no hypotheses on `f`;
* `Brockian.DilationGenerator.mellinLogSymm_mellinLog` and
  `Brockian.DilationGenerator.mellinLog_mellinLogSymm`: `U` and `U⁻¹` are
  mutually inverse (pointwise, on `(0, ∞)` resp. on `ℝ`);
* `Brockian.DilationGenerator.mellinLogUnitary`: the Lp upgrade — `U` as a
  surjective linear isometry (unitary)
  `L²((0,∞), dx) ≃ₗᵢ[𝕜] L²(ℝ, dt)`, with `U⁻¹` given by `mellinLogLpSymm`.

The first line of the file repeats the required header as a plain (non-doc)
comment, since Lean does not allow a module docstring before `import`.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.DilationGenerator

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E]

/-- The logarithmic substitution `x = eᵗ` applied to a function on `(0, ∞)`:
`(U f)(t) = e^{t/2} • f (eᵗ)`. -/
noncomputable def mellinLog [NormedSpace ℝ E] (f : ℝ → E) : ℝ → E :=
  fun t => Real.exp (t / 2) • f (Real.exp t)

/-- The inverse substitution `t = log x`: `(U⁻¹ h)(x) = x^{-1/2} • h (log x)`. -/
noncomputable def mellinLogSymm [NormedSpace ℝ E] (h : ℝ → E) : ℝ → E :=
  fun x => (Real.sqrt x)⁻¹ • h (Real.log x)

/-! ### The change of variables `x = eᵗ` at the level of measures -/

/-- The measure `eᵗ dt` on `ℝ`; it is the pullback of Lebesgue measure on `(0, ∞)`
along `t ↦ eᵗ`. -/
noncomputable def expWeightedMeasure : Measure ℝ :=
  (volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp t)

/-- The pushforward of the measure `eᵗ dt` under `exp` is Lebesgue measure on `(0, ∞)`. -/
theorem map_exp_withDensity_exp :
    Measure.map Real.exp expWeightedMeasure =
      (volume : Measure ℝ).restrict (Set.Ioi 0) := by
  have h := MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar (μ := (volume : Measure ℝ))
    (s := Set.univ) (f := Real.exp)
    (f' := fun t => (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Real.exp t)))
    MeasurableSet.univ.nullMeasurableSet
    (fun t _ => (Real.hasDerivAt_exp t).hasFDerivAt.hasFDerivWithinAt)
    Real.exp_injective.injOn
  rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at h
  simpa [expWeightedMeasure, ContinuousLinearMap.det, abs_of_pos (Real.exp_pos _)] using h

/-- `exp` is measure preserving from `(ℝ, eᵗ dt)` to `((0, ∞), dx)`. -/
theorem measurePreserving_exp :
    MeasurePreserving Real.exp expWeightedMeasure
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
  ⟨Real.measurable_exp, map_exp_withDensity_exp⟩

/-- `log` is measure preserving from `((0, ∞), dx)` to `(ℝ, eᵗ dt)`: the inverse
change of variables. -/
theorem measurePreserving_log :
    MeasurePreserving Real.log ((volume : Measure ℝ).restrict (Set.Ioi 0))
      expWeightedMeasure := by
  refine ⟨Real.measurable_log, ?_⟩
  rw [← map_exp_withDensity_exp, Measure.map_map Real.measurable_log Real.measurable_exp,
    show Real.log ∘ Real.exp = id from funext fun t => by simp, Measure.map_id]

theorem volume_absolutelyContinuous_expWeightedMeasure :
    (volume : Measure ℝ) ≪ expWeightedMeasure :=
  withDensity_absolutelyContinuous' (by fun_prop)
    (Filter.Eventually.of_forall fun t => by positivity)

theorem expWeightedMeasure_absolutelyContinuous_volume :
    expWeightedMeasure ≪ (volume : Measure ℝ) :=
  withDensity_absolutelyContinuous _ _

/-- Change of variables `x = eᵗ` for `ℝ≥0∞`-valued integrands; no hypotheses on `g`. -/
theorem lintegral_Ioi_eq_lintegral_exp (g : ℝ → ℝ≥0∞) :
    ∫⁻ x in Set.Ioi (0 : ℝ), g x = ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t) * g (Real.exp t) := by
  have h := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := (volume : Measure ℝ)) (s := Set.univ) (f := Real.exp)
    (f' := fun t => (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Real.exp t)))
    MeasurableSet.univ
    (fun t _ => (Real.hasDerivAt_exp t).hasFDerivAt.hasFDerivWithinAt)
    Real.exp_injective.injOn g
  rw [Set.image_univ, Real.range_exp] at h
  rw [h, MeasureTheory.setLIntegral_univ]
  simp [ContinuousLinearMap.det, abs_of_pos (Real.exp_pos _)]

/-! ### The `L²` identity -/

section NormedSpace

variable [NormedSpace ℝ E]

/-- **Mellin logarithmic unitarity.**  The substitution `x = eᵗ`, `(U f)(t) = e^{t/2} • f (eᵗ)`,
preserves the `L²` integral:
`∫_{(0,∞)} ‖f x‖² dx = ∫_ℝ ‖e^{t/2} • f (eᵗ)‖² dt`, for an arbitrary `f : ℝ → E`. -/
theorem mellin_log_unitary (f : ℝ → E) :
    ∫ x in Set.Ioi (0 : ℝ), ‖f x‖ ^ 2 = ∫ t : ℝ, ‖Real.exp (t / 2) • f (Real.exp t)‖ ^ 2 := by
  have h := integral_image_eq_integral_abs_deriv_smul (F := ℝ) MeasurableSet.univ
    (f := Real.exp) (f' := Real.exp)
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun x => ‖f x‖ ^ 2)
  rw [Set.image_univ, Real.range_exp] at h
  rw [h, setIntegral_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), smul_eq_mul]
  rw [← Real.exp_nat_mul]
  norm_num
  left; ring

/-- The target identity, phrased with the operator `mellinLog`. -/
theorem integral_norm_sq_mellinLog (f : ℝ → E) :
    ∫ x in Set.Ioi (0 : ℝ), ‖f x‖ ^ 2 = ∫ t : ℝ, ‖mellinLog f t‖ ^ 2 :=
  mellin_log_unitary f

/-- The `L²` seminorm identity in `ℝ≥0∞`, valid for every `f`: the unitarity of `U`
at the level of (extended) norms, with no integrability hypothesis. -/
theorem eLpNorm_mellinLog (f : ℝ → E) :
    eLpNorm (mellinLog (E := E) f) 2 (volume : Measure ℝ) =
      eLpNorm f 2 ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  congr 1
  rw [lintegral_Ioi_eq_lintegral_exp (fun x => ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal)]
  refine lintegral_congr fun t => ?_
  have hx : ‖mellinLog (E := E) f t‖ₑ = ENNReal.ofReal (Real.exp (t / 2)) * ‖f (Real.exp t)‖ₑ := by
    simp [mellinLog, enorm_smul, Real.enorm_eq_ofReal (Real.exp_nonneg _)]
  rw [hx, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  congr 1
  rw [ENNReal.toReal_ofNat, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
  norm_num

/-! ### `U` and `U⁻¹` are mutually inverse -/

/-- `U⁻¹ (U f) = f` on `(0, ∞)`. -/
theorem mellinLogSymm_mellinLog (f : ℝ → E) {x : ℝ} (hx : 0 < x) :
    mellinLogSymm (mellinLog f) x = f x := by
  have hlog : Real.exp (Real.log x) = x := Real.exp_log hx
  have h2 : Real.sqrt x = Real.exp (Real.log x / 2) := by
    have hxe : x = Real.exp (Real.log x / 2) * Real.exp (Real.log x / 2) := by
      rw [← Real.exp_add, show Real.log x / 2 + Real.log x / 2 = Real.log x by ring, hlog]
    conv_lhs => rw [hxe]
    exact Real.sqrt_mul_self (Real.exp_pos _).le
  simp only [mellinLogSymm, mellinLog, hlog, h2, smul_smul]
  rw [inv_mul_cancel₀ (by positivity), one_smul]

/-- `U (U⁻¹ h) = h` on `ℝ`. -/
theorem mellinLog_mellinLogSymm (h : ℝ → E) (t : ℝ) :
    mellinLog (mellinLogSymm h) t = h t := by
  have h1 : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
    have hte : Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hte, Real.sqrt_mul_self (Real.exp_pos _).le]
  simp only [mellinLog, mellinLogSymm, Real.log_exp, h1, smul_smul]
  rw [mul_inv_cancel₀ (by positivity), one_smul]

/-! ### Measurability, membership in `L²`, and compatibility with a.e. equality -/

theorem aestronglyMeasurable_mellinLog {f : ℝ → E}
    (hf : AEStronglyMeasurable f ((volume : Measure ℝ).restrict (Set.Ioi 0))) :
    AEStronglyMeasurable (mellinLog f) (volume : Measure ℝ) := by
  have h1 : AEStronglyMeasurable (f ∘ Real.exp) expWeightedMeasure :=
    hf.comp_measurePreserving measurePreserving_exp
  have h2 : AEStronglyMeasurable (f ∘ Real.exp) (volume : Measure ℝ) :=
    h1.mono_ac volume_absolutelyContinuous_expWeightedMeasure
  exact (Real.continuous_exp.comp (continuous_id.div_const 2)).aestronglyMeasurable.smul h2

theorem aestronglyMeasurable_mellinLogSymm {h : ℝ → E}
    (hh : AEStronglyMeasurable h (volume : Measure ℝ)) :
    AEStronglyMeasurable (mellinLogSymm h) ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  have h1 : AEStronglyMeasurable h expWeightedMeasure :=
    hh.mono_ac expWeightedMeasure_absolutelyContinuous_volume
  have h2 : AEStronglyMeasurable (h ∘ Real.log)
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    h1.comp_measurePreserving measurePreserving_log
  exact Real.continuous_sqrt.measurable.inv.aestronglyMeasurable.smul h2

theorem mellinLog_congr_ae {f g : ℝ → E}
    (h : f =ᵐ[(volume : Measure ℝ).restrict (Set.Ioi 0)] g) :
    mellinLog f =ᵐ[(volume : Measure ℝ)] mellinLog g := by
  have h1 : ∀ᵐ t ∂expWeightedMeasure, f (Real.exp t) = g (Real.exp t) :=
    measurePreserving_exp.quasiMeasurePreserving.ae h
  filter_upwards [volume_absolutelyContinuous_expWeightedMeasure h1] with t ht
  simp [mellinLog, ht]

theorem mellinLogSymm_congr_ae {h k : ℝ → E} (hhk : h =ᵐ[(volume : Measure ℝ)] k) :
    mellinLogSymm h =ᵐ[(volume : Measure ℝ).restrict (Set.Ioi 0)] mellinLogSymm k := by
  have h1 : ∀ᵐ x ∂expWeightedMeasure, h x = k x :=
    expWeightedMeasure_absolutelyContinuous_volume hhk
  filter_upwards [measurePreserving_log.quasiMeasurePreserving.ae h1] with x hx
  simp [mellinLogSymm, hx]

theorem memLp_mellinLog {f : ℝ → E}
    (hf : MemLp f 2 ((volume : Measure ℝ).restrict (Set.Ioi 0))) :
    MemLp (mellinLog f) 2 (volume : Measure ℝ) :=
  ⟨aestronglyMeasurable_mellinLog hf.1, by rw [eLpNorm_mellinLog]; exact hf.2⟩

theorem memLp_mellinLogSymm {h : ℝ → E} (hh : MemLp h 2 (volume : Measure ℝ)) :
    MemLp (mellinLogSymm h) 2 ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  refine ⟨aestronglyMeasurable_mellinLogSymm hh.1, ?_⟩
  have key := eLpNorm_mellinLog (mellinLogSymm h)
  rw [show mellinLog (mellinLogSymm h) = h from funext (mellinLog_mellinLogSymm h)] at key
  rw [← key]
  exact hh.2

/-! ### The unitary `L²(0, ∞) ≃ L²(ℝ)` -/

/-- The image of `f ∈ L²(0, ∞)` under `U`. -/
noncomputable def mellinLogLp (f : Lp E 2 ((volume : Measure ℝ).restrict (Set.Ioi 0))) :
    Lp E 2 (volume : Measure ℝ) :=
  (memLp_mellinLog (Lp.memLp f)).toLp _

/-- The image of `h ∈ L²(ℝ)` under `U⁻¹`. -/
noncomputable def mellinLogLpSymm (h : Lp E 2 (volume : Measure ℝ)) :
    Lp E 2 ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
  (memLp_mellinLogSymm (Lp.memLp h)).toLp _

theorem coeFn_mellinLogLp (f : Lp E 2 ((volume : Measure ℝ).restrict (Set.Ioi 0))) :
    ⇑(mellinLogLp f) =ᵐ[(volume : Measure ℝ)] mellinLog ⇑f :=
  MemLp.coeFn_toLp _

theorem coeFn_mellinLogLpSymm (h : Lp E 2 (volume : Measure ℝ)) :
    ⇑(mellinLogLpSymm h) =ᵐ[(volume : Measure ℝ).restrict (Set.Ioi 0)] mellinLogSymm ⇑h :=
  MemLp.coeFn_toLp _

theorem mellinLogLp_add (f g : Lp E 2 ((volume : Measure ℝ).restrict (Set.Ioi 0))) :
    mellinLogLp (f + g) = mellinLogLp f + mellinLogLp g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mellinLogLp (f + g), coeFn_mellinLogLp f, coeFn_mellinLogLp g,
    Lp.coeFn_add (mellinLogLp f) (mellinLogLp g), mellinLog_congr_ae (Lp.coeFn_add f g)]
    with t h1 h2 h3 h4 h5
  rw [h1, h4]
  simp only [Pi.add_apply]
  rw [h2, h3, h5]
  simp [mellinLog, smul_add]

theorem mellinLogLp_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] (c : 𝕜)
    (f : Lp E 2 ((volume : Measure ℝ).restrict (Set.Ioi 0))) :
    mellinLogLp (c • f) = c • mellinLogLp f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mellinLogLp (c • f), coeFn_mellinLogLp f,
    Lp.coeFn_smul c (mellinLogLp f), mellinLog_congr_ae (Lp.coeFn_smul c f)]
    with t h1 h2 h3 h4
  rw [h1, h3]
  simp only [Pi.smul_apply]
  rw [h2, h4]
  simp only [mellinLog, Pi.smul_apply]
  exact smul_comm _ _ _

theorem mellinLogLpSymm_mellinLogLp (f : Lp E 2 ((volume : Measure ℝ).restrict (Set.Ioi 0))) :
    mellinLogLpSymm (mellinLogLp f) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mellinLogLpSymm (mellinLogLp f),
    mellinLogSymm_congr_ae (coeFn_mellinLogLp f),
    ae_restrict_mem measurableSet_Ioi] with x h1 h2 hx
  rw [h1, h2, mellinLogSymm_mellinLog _ hx]

theorem mellinLogLp_mellinLogLpSymm (h : Lp E 2 (volume : Measure ℝ)) :
    mellinLogLp (mellinLogLpSymm h) = h := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mellinLogLp (mellinLogLpSymm h),
    mellinLog_congr_ae (coeFn_mellinLogLpSymm h)] with t h1 h2
  rw [h1, h2, mellinLog_mellinLogSymm]

theorem norm_mellinLogLp (f : Lp E 2 ((volume : Measure ℝ).restrict (Set.Ioi 0))) :
    ‖mellinLogLp f‖ = ‖f‖ := by
  rw [mellinLogLp, Lp.norm_toLp, eLpNorm_mellinLog, ← Lp.norm_def]

/-- **The Mellin logarithmic unitary** `U : L²(0, ∞) ≃ L²(ℝ)`, `(U f)(t) = e^{t/2} f(eᵗ)`,
with inverse `(U⁻¹ h)(x) = x^{-1/2} h(log x)`: a surjective linear isometry. -/
noncomputable def mellinLogUnitary (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] :
    Lp E 2 ((volume : Measure ℝ).restrict (Set.Ioi 0)) ≃ₗᵢ[𝕜] Lp E 2 (volume : Measure ℝ) where
  toFun := mellinLogLp
  invFun := mellinLogLpSymm
  left_inv := mellinLogLpSymm_mellinLogLp
  right_inv := mellinLogLp_mellinLogLpSymm
  map_add' := mellinLogLp_add
  map_smul' := mellinLogLp_smul
  norm_map' := norm_mellinLogLp

@[simp] theorem mellinLogUnitary_apply (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] (f : Lp E 2 ((volume : Measure ℝ).restrict (Set.Ioi 0))) :
    mellinLogUnitary (E := E) 𝕜 f = mellinLogLp f := rfl

@[simp] theorem mellinLogUnitary_symm_apply (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] (h : Lp E 2 (volume : Measure ℝ)) :
    (mellinLogUnitary (E := E) 𝕜).symm h = mellinLogLpSymm h := rfl

end NormedSpace

end Brockian.DilationGenerator

