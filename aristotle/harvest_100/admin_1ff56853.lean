/-
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`; the required header
-- appears verbatim above as a block comment and is repeated as a module docstring below.)
import Mathlib

/-!
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

The substitution `x = e^t` induces a unitary `U : L²(0,∞) ≃ L²(ℝ)`,
`(U f)(t) = e^{t/2} · f(e^t)`, with inverse `(U⁻¹ h)(x) = x^{-1/2} · h(log x)`.

* `Brockian.DilationGenerator.mellin_log_unitary` — the target: the change of variables identity
  `∫_{(0,∞)} ‖f x‖² dx = ∫_ℝ ‖e^{t/2} • f(e^t)‖² dt`, valid for every `f : ℝ → E`.
* `Brockian.DilationGenerator.mellin_log_unitary_symm` — the same for the inverse substitution.
* `Brockian.DilationGenerator.mellinLogLpEquiv` — the upgrade to the `Lp` API: a linear isometry
  equivalence `L²((0,∞)) ≃ₗᵢ L²(ℝ)` implementing `f ↦ (t ↦ e^{t/2} • f (e^t))`.
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

/-! ### The change of variables `x = exp t` -/

/-- The exponential map sends `ℝ` onto the positive half-line. -/
lemma image_exp_univ : Real.exp '' Set.univ = Set.Ioi (0 : ℝ) := by
  simp [Real.range_exp]

/-- Change of variables `x = exp t` for Bochner integrals over the half line `(0, ∞)`.
This is the substitution underlying the Mellin/logarithmic change of variables. -/
theorem integral_Ioi_eq_integral_exp_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ → F) :
    ∫ x in Set.Ioi (0 : ℝ), g x = ∫ t : ℝ, Real.exp t • g (Real.exp t) := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := Real.exp) (f' := Real.exp)
      (s := Set.univ) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn g
  rw [image_exp_univ] at h
  simpa [abs_of_pos (Real.exp_pos _), Measure.restrict_univ] using h

/-- Change of variables `x = exp t` for Lebesgue (`ℝ≥0∞`-valued) integrals over `(0, ∞)`.
No measurability hypothesis is needed. -/
theorem lintegral_Ioi_eq_lintegral_exp_mul (g : ℝ → ENNReal) :
    ∫⁻ x in Set.Ioi (0 : ℝ), g x
      = ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t) * g (Real.exp t) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
      (s := Set.univ) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn g
  rw [image_exp_univ] at h
  simpa [abs_of_pos (Real.exp_pos _), Measure.restrict_univ] using h

/-! ### The Mellin logarithmic substitution and its inverse -/

/-- `(U f)(t) = e^{t/2} • f (e^t)`, the logarithmic substitution on functions. -/
noncomputable def mellinLogMap (f : ℝ → E) : ℝ → E := fun t => Real.exp (t / 2) • f (Real.exp t)

/-- `(U⁻¹ h)(x) = x^{-1/2} • h (log x)`, the inverse logarithmic substitution on functions. -/
noncomputable def mellinLogMapSymm (h : ℝ → E) : ℝ → E :=
  fun x => (x ^ (-(1 : ℝ) / 2) : ℝ) • h (Real.log x)

/-- The squared norm of the transformed function: `‖e^{t/2} • f(e^t)‖² = e^t · ‖f(e^t)‖²`. -/
lemma norm_sq_exp_half_smul (f : ℝ → E) (t : ℝ) :
    ‖Real.exp (t / 2) • f (Real.exp t)‖ ^ 2 = Real.exp t * ‖f (Real.exp t)‖ ^ 2 := by
  have h2 : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, h2]

/-- **Mellin logarithmic substitution is norm preserving.**

The substitution `x = e^t` turns the `L²(0, ∞)` norm into the `L²(ℝ)` norm of
`(U f)(t) = e^{t/2} · f(e^t)`:
`∫_{(0,∞)} ‖f x‖² dx = ∫_ℝ ‖e^{t/2} • f(e^t)‖² dt`.

The identity holds for an arbitrary function `f : ℝ → E` into a real normed space (both sides
are `0` when the integrand fails to be integrable, by the convention of the Bochner integral). -/
theorem mellin_log_unitary (f : ℝ → E) :
    ∫ x in Set.Ioi (0 : ℝ), ‖f x‖ ^ 2 = ∫ t : ℝ, ‖Real.exp (t / 2) • f (Real.exp t)‖ ^ 2 := by
  rw [integral_Ioi_eq_integral_exp_smul (fun x => ‖f x‖ ^ 2)]
  refine integral_congr_ae (.of_forall fun t => ?_)
  simp only [smul_eq_mul, norm_sq_exp_half_smul f t]

/-- The inverse substitution `(U⁻¹ h)(x) = x^{-1/2} · h (log x)` is norm preserving in the other
direction: `∫_ℝ ‖h t‖² dt = ∫_{(0,∞)} ‖x^{-1/2} • h (log x)‖² dx`. -/
theorem mellin_log_unitary_symm (h : ℝ → E) :
    ∫ t : ℝ, ‖h t‖ ^ 2
      = ∫ x in Set.Ioi (0 : ℝ), ‖(x ^ (-(1 : ℝ) / 2) : ℝ) • h (Real.log x)‖ ^ 2 := by
  rw [mellin_log_unitary (fun x => (x ^ (-(1 : ℝ) / 2) : ℝ) • h (Real.log x))]
  refine integral_congr_ae (.of_forall fun t => ?_)
  have hrpow : (Real.exp t) ^ (-(1 : ℝ) / 2) = Real.exp (-(t / 2)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]; ring_nf
  simp only [Real.log_exp, hrpow, smul_smul, ← Real.exp_add]
  norm_num

/-- Pointwise, `U⁻¹ ∘ U = id` on `(0, ∞)`. -/
theorem mellinLogMapSymm_mellinLogMap (f : ℝ → E) {x : ℝ} (hx : 0 < x) :
    mellinLogMapSymm (mellinLogMap f) x = f x := by
  have hexp : Real.exp (Real.log x) = x := Real.exp_log hx
  have hhalf : Real.exp (Real.log x / 2) = x ^ ((1 : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos hx]; ring_nf
  simp only [mellinLogMap, mellinLogMapSymm]
  rw [hexp, hhalf, smul_smul, ← Real.rpow_add hx]
  norm_num

/-- Pointwise, `U ∘ U⁻¹ = id` on `ℝ`. -/
theorem mellinLogMap_mellinLogMapSymm (h : ℝ → E) : mellinLogMap (mellinLogMapSymm h) = h := by
  funext t
  have hrpow : (Real.exp t) ^ (-(1 : ℝ) / 2) = Real.exp (-(t / 2)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]; ring_nf
  simp only [mellinLogMap, mellinLogMapSymm, Real.log_exp, hrpow, smul_smul, ← Real.exp_add]
  norm_num

/-! ### Quasi measure preserving properties of `exp` and `log` -/

/-- `exp` pushes the Lebesgue measure on `ℝ` to a measure absolutely continuous with respect to
the Lebesgue measure on `(0, ∞)`. -/
lemma quasiMeasurePreserving_exp :
    Measure.QuasiMeasurePreserving Real.exp volume (volume.restrict (Set.Ioi (0 : ℝ))) := by
  refine ⟨Real.measurable_exp, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply Real.measurable_exp hs]
  have key := lintegral_Ioi_eq_lintegral_exp_mul (s.indicator 1)
  rw [lintegral_indicator_one hs, hs0] at key
  have hF : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp t) * s.indicator 1 (Real.exp t)) :=
    (ENNReal.measurable_ofReal.comp Real.measurable_exp).mul
      ((measurable_const.indicator hs).comp Real.measurable_exp)
  have h0 := (lintegral_eq_zero_iff hF).mp key.symm
  have hae : ∀ᵐ t : ℝ, t ∉ Real.exp ⁻¹' s := by
    filter_upwards [h0] with t ht
    simp only [Pi.zero_apply, mul_eq_zero] at ht
    rcases ht with h | h
    · exact absurd h (by positivity)
    · intro hmem
      rw [Set.indicator_of_mem (show Real.exp t ∈ s from hmem)] at h
      simp at h
  rwa [← MeasureTheory.measure_eq_zero_iff_ae_notMem] at hae

/-- `log` pushes the Lebesgue measure on `(0, ∞)` to a measure absolutely continuous with respect
to the Lebesgue measure on `ℝ`. -/
lemma quasiMeasurePreserving_log :
    Measure.QuasiMeasurePreserving Real.log (volume.restrict (Set.Ioi (0 : ℝ))) volume := by
  refine ⟨Real.measurable_log, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply Real.measurable_log hs]
  have key := lintegral_Ioi_eq_lintegral_exp_mul ((Real.log ⁻¹' s).indicator 1)
  rw [lintegral_indicator_one (hs.preimage Real.measurable_log)] at key
  rw [key]
  have hpt : ∀ t : ℝ, ENNReal.ofReal (Real.exp t) * (Real.log ⁻¹' s).indicator 1 (Real.exp t)
      = s.indicator (fun t => ENNReal.ofReal (Real.exp t)) t := by
    intro t
    by_cases ht : t ∈ s
    · rw [Set.indicator_of_mem (show Real.exp t ∈ Real.log ⁻¹' s by simpa [Real.log_exp] using ht),
        Set.indicator_of_mem ht]
      simp
    · rw [Set.indicator_of_notMem (by simpa [Real.log_exp] using ht),
        Set.indicator_of_notMem ht]
      simp
  simp_rw [hpt]
  rw [lintegral_indicator hs, Measure.restrict_eq_zero.mpr hs0, lintegral_zero_measure]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Almost everywhere equality is preserved by precomposition with `exp`. -/
lemma aeEq_comp_exp {f g : ℝ → E} (h : f =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] g) :
    (fun t => f (Real.exp t)) =ᵐ[volume] fun t => g (Real.exp t) :=
  h.comp_tendsto quasiMeasurePreserving_exp.tendsto_ae

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Almost everywhere equality is preserved by precomposition with `log`. -/
lemma aeEq_comp_log {f g : ℝ → E} (h : f =ᵐ[volume] g) :
    (fun x => f (Real.log x)) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] fun x => g (Real.log x) :=
  h.comp_tendsto quasiMeasurePreserving_log.tendsto_ae

/-! ### The `L²` norms agree -/

lemma enorm_sq_mellinLogMap (f : ℝ → E) (t : ℝ) :
    ‖mellinLogMap f t‖ₑ ^ (2 : ℝ)
      = ENNReal.ofReal (Real.exp t) * ‖f (Real.exp t)‖ₑ ^ (2 : ℝ) := by
  have h2 : Real.exp (t / 2) ^ (2 : ℝ) = Real.exp t := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]; ring_nf
  rw [mellinLogMap, enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  congr 1
  rw [Real.enorm_eq_ofReal (Real.exp_pos _).le, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), h2]

/-- The `L²` seminorm is preserved by the logarithmic substitution, for every function. -/
theorem eLpNorm_mellinLogMap (f : ℝ → E) :
    eLpNorm (mellinLogMap f) 2 volume = eLpNorm f 2 (volume.restrict (Set.Ioi (0 : ℝ))) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  congr 1
  rw [show ((2 : ENNReal).toReal) = (2 : ℝ) by norm_num,
      lintegral_Ioi_eq_lintegral_exp_mul (fun x => ‖f x‖ₑ ^ (2 : ℝ))]
  exact lintegral_congr fun t => enorm_sq_mellinLogMap f t

/-- The `L²` seminorm is preserved by the inverse logarithmic substitution. -/
theorem eLpNorm_mellinLogMapSymm (h : ℝ → E) :
    eLpNorm (mellinLogMapSymm h) 2 (volume.restrict (Set.Ioi (0 : ℝ)))
      = eLpNorm h 2 volume := by
  rw [← eLpNorm_mellinLogMap (mellinLogMapSymm h), mellinLogMap_mellinLogMapSymm]

/-! ### The unitary on `L²` -/

lemma aestronglyMeasurable_mellinLogMap {f : ℝ → E}
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioi (0 : ℝ)))) :
    AEStronglyMeasurable (mellinLogMap f) volume :=
  (Real.continuous_exp.comp (continuous_id.div_const 2)).aestronglyMeasurable.smul
    (hf.comp_quasiMeasurePreserving quasiMeasurePreserving_exp)

lemma aestronglyMeasurable_mellinLogMapSymm {h : ℝ → E} (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (mellinLogMapSymm h) (volume.restrict (Set.Ioi (0 : ℝ))) :=
  (show Measurable (fun x : ℝ => x ^ (-(1 : ℝ) / 2)) by
      fun_prop).aestronglyMeasurable.smul
    (hh.comp_quasiMeasurePreserving quasiMeasurePreserving_log)

lemma memLp_mellinLogMap {f : ℝ → E} (hf : MemLp f 2 (volume.restrict (Set.Ioi (0 : ℝ)))) :
    MemLp (mellinLogMap f) 2 volume :=
  ⟨aestronglyMeasurable_mellinLogMap hf.1, by rw [eLpNorm_mellinLogMap]; exact hf.2⟩

lemma memLp_mellinLogMapSymm {h : ℝ → E} (hh : MemLp h 2 volume) :
    MemLp (mellinLogMapSymm h) 2 (volume.restrict (Set.Ioi (0 : ℝ))) :=
  ⟨aestronglyMeasurable_mellinLogMapSymm hh.1, by rw [eLpNorm_mellinLogMapSymm]; exact hh.2⟩

variable {𝕂 : Type*} [NontriviallyNormedField 𝕂] [NormedSpace 𝕂 E] [SMulCommClass ℝ 𝕂 E]

/-- The map `U : L²((0,∞)) → L²(ℝ)`, `f ↦ (t ↦ e^{t/2} • f (e^t))`. -/
noncomputable def mellinLogLp (F : Lp E 2 (volume.restrict (Set.Ioi (0 : ℝ)))) :
    Lp E 2 (volume : Measure ℝ) :=
  MemLp.toLp _ (memLp_mellinLogMap (Lp.memLp F))

/-- The map `U⁻¹ : L²(ℝ) → L²((0,∞))`, `h ↦ (x ↦ x^{-1/2} • h (log x))`. -/
noncomputable def mellinLogLpSymm (H : Lp E 2 (volume : Measure ℝ)) :
    Lp E 2 (volume.restrict (Set.Ioi (0 : ℝ))) :=
  MemLp.toLp _ (memLp_mellinLogMapSymm (Lp.memLp H))

lemma coeFn_mellinLogLp (F : Lp E 2 (volume.restrict (Set.Ioi (0 : ℝ)))) :
    ⇑(mellinLogLp F) =ᵐ[volume] mellinLogMap ⇑F := MemLp.coeFn_toLp _

lemma coeFn_mellinLogLpSymm (H : Lp E 2 (volume : Measure ℝ)) :
    ⇑(mellinLogLpSymm H) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] mellinLogMapSymm ⇑H :=
  MemLp.coeFn_toLp _

lemma mellinLogLp_add (F G : Lp E 2 (volume.restrict (Set.Ioi (0 : ℝ)))) :
    mellinLogLp (F + G) = mellinLogLp F + mellinLogLp G := by
  refine Lp.ext ?_
  filter_upwards [aeEq_comp_exp (Lp.coeFn_add F G), coeFn_mellinLogLp (F + G),
    Lp.coeFn_add (mellinLogLp F) (mellinLogLp G), coeFn_mellinLogLp F,
    coeFn_mellinLogLp G] with t e1 e2 e3 e4 e5
  rw [e2, e3, Pi.add_apply, e4, e5]
  simp only [mellinLogMap]
  rw [e1]
  simp [smul_add]

lemma mellinLogLp_smul (c : 𝕂) (F : Lp E 2 (volume.restrict (Set.Ioi (0 : ℝ)))) :
    mellinLogLp (c • F) = c • mellinLogLp F := by
  refine Lp.ext ?_
  filter_upwards [aeEq_comp_exp (Lp.coeFn_smul c F), coeFn_mellinLogLp (c • F),
    Lp.coeFn_smul c (mellinLogLp F), coeFn_mellinLogLp F] with t e1 e2 e3 e4
  rw [e2, e3, Pi.smul_apply, e4]
  simp only [mellinLogMap]
  rw [e1]
  simp [smul_comm]

lemma mellinLogLpSymm_mellinLogLp (F : Lp E 2 (volume.restrict (Set.Ioi (0 : ℝ)))) :
    mellinLogLpSymm (mellinLogLp F) = F := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mellinLogLpSymm (mellinLogLp F), aeEq_comp_log (coeFn_mellinLogLp F),
    ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with x e1 e2 hx
  rw [e1]
  simp only [mellinLogMapSymm]
  rw [e2]
  exact mellinLogMapSymm_mellinLogMap (⇑F) hx

lemma mellinLogLp_mellinLogLpSymm (H : Lp E 2 (volume : Measure ℝ)) :
    mellinLogLp (mellinLogLpSymm H) = H := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mellinLogLp (mellinLogLpSymm H),
    aeEq_comp_exp (coeFn_mellinLogLpSymm H)] with t e1 e2
  rw [e1]
  simp only [mellinLogMap]
  rw [e2]
  exact congrFun (mellinLogMap_mellinLogMapSymm (⇑H)) t

lemma norm_mellinLogLp (F : Lp E 2 (volume.restrict (Set.Ioi (0 : ℝ)))) :
    ‖mellinLogLp F‖ = ‖F‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_mellinLogLp F), eLpNorm_mellinLogMap]

/-- **The Mellin logarithmic substitution as a unitary.**

The substitution `x = e^t` induces a linear isometry equivalence
`L²((0,∞)) ≃ₗᵢ L²(ℝ)` given by `(U f)(t) = e^{t/2} • f (e^t)`, with inverse
`(U⁻¹ h)(x) = x^{-1/2} • h (log x)`. Taking `𝕂 = ℂ` and `E = ℂ` this is the usual unitary
implementing the Mellin transform as a Fourier transform. -/
noncomputable def mellinLogLpEquiv :
    Lp E 2 (volume.restrict (Set.Ioi (0 : ℝ))) ≃ₗᵢ[𝕂] Lp E 2 (volume : Measure ℝ) where
  toFun := mellinLogLp
  map_add' := mellinLogLp_add
  map_smul' := mellinLogLp_smul
  invFun := mellinLogLpSymm
  left_inv := mellinLogLpSymm_mellinLogLp
  right_inv := mellinLogLp_mellinLogLpSymm
  norm_map' := norm_mellinLogLp

@[simp] lemma mellinLogLpEquiv_apply (F : Lp E 2 (volume.restrict (Set.Ioi (0 : ℝ)))) :
    (mellinLogLpEquiv (𝕂 := 𝕂)) F = mellinLogLp F := rfl

@[simp] lemma mellinLogLpEquiv_symm_apply (H : Lp E 2 (volume : Measure ℝ)) :
    (mellinLogLpEquiv (𝕂 := 𝕂)).symm H = mellinLogLpSymm H := rfl

/-- The unitary acts, almost everywhere, by `f ↦ (t ↦ e^{t/2} • f (e^t))`. -/
theorem coeFn_mellinLogLpEquiv (F : Lp E 2 (volume.restrict (Set.Ioi (0 : ℝ)))) :
    ⇑((mellinLogLpEquiv (𝕂 := 𝕂)) F) =ᵐ[volume]
      fun t => Real.exp (t / 2) • (F : ℝ → E) (Real.exp t) :=
  coeFn_mellinLogLp F

/-- The inverse unitary acts, almost everywhere, by `h ↦ (x ↦ x^{-1/2} • h (log x))`. -/
theorem coeFn_mellinLogLpEquiv_symm (H : Lp E 2 (volume : Measure ℝ)) :
    ⇑((mellinLogLpEquiv (𝕂 := 𝕂)).symm H) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun x => (x ^ (-(1 : ℝ) / 2) : ℝ) • (H : ℝ → E) (Real.log x) :=
  coeFn_mellinLogLpSymm H

end DilationGenerator
end Brockian

