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

open scoped Real ENNReal
open MeasureTheory Set

namespace Brockian
namespace DilationGenerator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The image of `ℝ` under `exp` is the positive half line. -/
lemma image_exp_univ : Real.exp '' (univ : Set ℝ) = Ioi (0 : ℝ) := by
  rw [Set.image_univ, Real.range_exp]

/-- The map `U : f ↦ (t ↦ e^{t/2} • f (e^t))` used to identify `L²(0,∞)` with `L²(ℝ)`. -/
noncomputable def mellinLogMap (f : ℝ → E) : ℝ → E :=
  fun t => Real.exp (t / 2) • f (Real.exp t)

/-- The candidate inverse map `U⁻¹ : h ↦ (x ↦ x^{-1/2} • h (log x))`. -/
noncomputable def mellinLogMapInv (h : ℝ → E) : ℝ → E :=
  fun x => (x ^ (-(1 : ℝ) / 2)) • h (Real.log x)

lemma exp_half_sq (t : ℝ) : Real.exp (t / 2) ^ 2 = Real.exp t := by
  rw [sq, ← Real.exp_add]
  ring_nf

/-- Pointwise form of the Jacobian factor: `‖e^{t/2} • f (e^t)‖² = e^t ‖f (e^t)‖²`. -/
lemma norm_sq_mellinLogMap (f : ℝ → E) (t : ℝ) :
    ‖mellinLogMap f t‖ ^ 2 = Real.exp t * ‖f (Real.exp t)‖ ^ 2 := by
  simp only [mellinLogMap, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
    exp_half_sq]

/-- `U⁻¹ ∘ U = id` on the positive half line. -/
lemma mellinLogMapInv_mellinLogMap (f : ℝ → E) {x : ℝ} (hx : 0 < x) :
    mellinLogMapInv (mellinLogMap f) x = f x := by
  have hlog : Real.exp (Real.log x) = x := Real.exp_log hx
  simp only [mellinLogMapInv, mellinLogMap, hlog, smul_smul]
  rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
  have : Real.log x * (-(1 : ℝ) / 2) + Real.log x / 2 = 0 := by ring
  rw [this, Real.exp_zero, one_smul]

/-- `U ∘ U⁻¹ = id` on `ℝ`. -/
lemma mellinLogMap_mellinLogMapInv (h : ℝ → E) (t : ℝ) :
    mellinLogMap (mellinLogMapInv h) t = h t := by
  have hlog : Real.log (Real.exp t) = t := Real.log_exp t
  simp only [mellinLogMap, mellinLogMapInv, hlog, smul_smul]
  rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp, ← Real.exp_add]
  have hz : t / 2 + t * (-(1 : ℝ) / 2) = 0 := by ring
  rw [hz, Real.exp_zero, one_smul]

/-- **Change of variables `x = e^t`** for Lebesgue (`ℝ≥0∞`-valued) integrals: no integrability
assumption is needed. -/
theorem lintegral_comp_exp (g : ℝ → ℝ≥0∞) :
    ∫⁻ x in Ioi (0 : ℝ), g x = ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t) * g (Real.exp t) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn g
  rw [image_exp_univ, Measure.restrict_univ] at h
  simpa only [abs_of_pos (Real.exp_pos _)] using h

/-- The `L²`-Lebesgue integral is preserved by `U`, with no integrability assumption. -/
theorem lintegral_enorm_sq_mellinLogMap (f : ℝ → E) :
    ∫⁻ x in Ioi (0 : ℝ), ‖f x‖ₑ ^ 2 = ∫⁻ t : ℝ, ‖mellinLogMap f t‖ₑ ^ 2 := by
  rw [lintegral_comp_exp (fun x => ‖f x‖ₑ ^ 2)]
  refine lintegral_congr (fun t => ?_)
  have h1 : ‖mellinLogMap f t‖ₑ ^ 2 = ENNReal.ofReal (‖mellinLogMap f t‖ ^ 2) := by
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have h2 : ‖f (Real.exp t)‖ₑ ^ 2 = ENNReal.ofReal (‖f (Real.exp t)‖ ^ 2) := by
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [h1, h2, norm_sq_mellinLogMap, ENNReal.ofReal_mul (Real.exp_pos t).le]

/-- The `L²` norm (as an `eLpNorm`) is preserved by `U`: this is the "unitarity" statement at the
level of norms. -/
theorem eLpNorm_mellinLogMap (f : ℝ → E) :
    eLpNorm (mellinLogMap f) 2 volume = eLpNorm f 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hpt : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  have htr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [htr]
  congr 1
  have hpow : ∀ (a : ℝ≥0∞), a ^ (2 : ℝ) = a ^ (2 : ℕ) := by
    intro a
    rw [← ENNReal.rpow_natCast a 2]
    norm_num
  simp only [hpow]
  exact (lintegral_enorm_sq_mellinLogMap f).symm

/-- **Mellin log unitary (integral form).**
The substitution `x = eᵗ` turns the `L²(0,∞)` integral of `f` into the `L²(ℝ)` integral of
`U f : t ↦ e^{t/2} • f (eᵗ)`. No integrability or measurability hypothesis is required: if one
side fails to be integrable, so does the other, and both integrals are then `0`. -/
theorem mellin_log_unitary (f : ℝ → E) :
    ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 = ∫ t : ℝ, ‖Real.exp (t / 2) • f (Real.exp t)‖ ^ 2 := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := Real.exp) (f' := Real.exp)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun x => ‖f x‖ ^ 2)
  rw [image_exp_univ, Measure.restrict_univ] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, smul_eq_mul,
    exp_half_sq]

/-- The inverse substitution `t = log x`: the `L²(ℝ)` integral of `h` equals the `L²(0,∞)`
integral of `U⁻¹ h : x ↦ x^{-1/2} • h (log x)`. -/
theorem mellin_log_unitary_inv (h : ℝ → E) :
    ∫ t : ℝ, ‖h t‖ ^ 2
      = ∫ x in Ioi (0 : ℝ), ‖(x ^ (-(1 : ℝ) / 2)) • h (Real.log x)‖ ^ 2 := by
  have key := mellin_log_unitary (mellinLogMapInv h)
  have hcongr : ∀ t : ℝ, ‖Real.exp (t / 2) • mellinLogMapInv h (Real.exp t)‖ ^ 2 = ‖h t‖ ^ 2 := by
    intro t
    rw [show Real.exp (t / 2) • mellinLogMapInv h (Real.exp t) = mellinLogMap
      (mellinLogMapInv h) t from rfl, mellinLogMap_mellinLogMapInv]
  rw [integral_congr_ae (Filter.Eventually.of_forall hcongr)] at key
  exact key.symm

/-- `f` is `L²` on `(0,∞)` if and only if `U f` is `L²` on `ℝ`. -/
theorem memLp_mellinLogMap_iff (f : ℝ → E) (hf : AEStronglyMeasurable f
    (volume.restrict (Ioi (0 : ℝ)))) (hUf : AEStronglyMeasurable (mellinLogMap f) volume) :
    MemLp (mellinLogMap f) 2 volume ↔ MemLp f 2 (volume.restrict (Ioi (0 : ℝ))) := by
  constructor
  · intro hm
    exact ⟨hf, by rw [← eLpNorm_mellinLogMap]; exact hm.2⟩
  · intro hm
    exact ⟨hUf, by rw [eLpNorm_mellinLogMap]; exact hm.2⟩

end DilationGenerator
end Brockian

