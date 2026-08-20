/-!
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Statement: The substitution x = e^t induces a unitary U : L²(0,∞) ≃ L²(ℝ), (U f)(t) = e^{t/2}·f(e^t) — norm-preserving with inverse (U⁻¹ h)(x) = x^{-1/2}·h(log x).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The substitution `x = e^t` induces a unitary `U : L²(0,∞) ≃ L²(ℝ)`,
`(U f)(t) = e^{t/2} · f(e^t)`, with inverse `(U⁻¹ h)(x) = x^{-1/2} · h(log x)`.

We formalise this at the level of integrals and `L²`-seminorms:

* `Brockian.DilationGenerator.mellin_log_unitary` — the Bochner integral identity
  `∫ x in Ioi 0, ‖f x‖² = ∫ t, ‖e^{t/2} • f (e^t)‖²`, with no hypotheses on `f`;
* `Brockian.DilationGenerator.lintegral_norm_sq_comp_exp` — the same identity for the
  lower Lebesgue integral (so it also carries the information that one side is infinite
  exactly when the other is);
* `Brockian.DilationGenerator.eLpNorm_comp_exp` — consequently `U` preserves the
  `L²`-seminorm, `eLpNorm f 2 (volume.restrict (Ioi 0)) = eLpNorm (U f) 2 volume`;
* `Brockian.DilationGenerator.mellin_log_unitary_symm` — the corresponding identity for
  the inverse substitution `x ↦ x^{-1/2} • h (log x)`;
* `Brockian.DilationGenerator.measurePreserving_exp_withDensity` — the underlying pushforward
  statement: `Real.exp` maps the weighted measure `e^t dt` on `ℝ` to Lebesgue measure on `(0,∞)`;
* `Brockian.DilationGenerator.mellin_log_inv_apply` and
  `Brockian.DilationGenerator.mellin_log_apply_inv` — the two pointwise inversion
  identities, showing the displayed formulas are mutually inverse.

The key input is the one-dimensional change-of-variables formula
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` (and its `lintegral` counterpart
`MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul`) applied to `Real.exp`, whose image
of `univ` is `Ioi 0` and whose derivative is `exp`.

BLOCKED: packaging these statements into a `LinearIsometryEquiv (Lp E 2 (volume.restrict (Ioi 0)))
(Lp E 2 volume)` is not carried out here; it additionally requires the quotient-level
well-definedness of `f ↦ (fun t => e^{t/2} • f (e^t))` on a.e.-equivalence classes and a surjectivity
argument, which are left for future work.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open MeasureTheory Set

namespace Brockian
namespace DilationGenerator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem exp_image_univ : Real.exp '' univ = Ioi (0 : ℝ) := by
  rw [Set.image_univ, Real.range_exp]

private theorem exp_eq_sq_exp_half (t : ℝ) : Real.exp t = Real.exp (t / 2) ^ 2 := by
  rw [sq, ← Real.exp_add]; ring_nf

/-- The change of variables `x = exp t` identifies the `L²`-norm on `(0, ∞)` with the `L²`-norm
on `ℝ` after the substitution `f ↦ (fun t => exp (t / 2) • f (exp t))`.

This is the analytic heart of the statement that the logarithmic (Mellin) substitution
`U : L²(0,∞) ≃ L²(ℝ)`, `(U f)(t) = e^{t/2} f(e^t)`, is unitary: it says that `U` preserves the
squared `L²` integral. No hypotheses on `f` are needed, since the change-of-variables formula
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` holds for an arbitrary integrand. -/
theorem mellin_log_unitary (f : ℝ → E) :
    ∫ x in Set.Ioi (0 : ℝ), ‖f x‖ ^ 2 = ∫ t : ℝ, ‖Real.exp (t / 2) • f (Real.exp t)‖ ^ 2 := by
  rw [← exp_image_univ, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    setIntegral_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), smul_eq_mul, mul_pow]
  rw [exp_eq_sq_exp_half t]

/-- The `lintegral` form of `mellin_log_unitary`: the substitution `x = exp t` preserves the
squared `L²` integral, computed in `ℝ≥0∞`. In particular one side is infinite exactly when the
other one is. -/
theorem lintegral_norm_sq_comp_exp (f : ℝ → E) :
    ∫⁻ x in Set.Ioi (0 : ℝ), ‖f x‖ₑ ^ 2 = ∫⁻ t : ℝ, ‖Real.exp (t / 2) • f (Real.exp t)‖ₑ ^ 2 := by
  rw [← exp_image_univ, lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    setLIntegral_univ]
  refine lintegral_congr fun t => ?_
  rw [enorm_smul, mul_pow, Real.enorm_eq_ofReal (Real.exp_pos _).le,
    abs_of_pos (Real.exp_pos _), ← ENNReal.ofReal_pow (Real.exp_pos _).le, exp_eq_sq_exp_half t]

/-- The substitution `x = exp t` preserves the `L²` seminorm: it is an isometry from
`L²((0,∞), dx)` to `L²(ℝ, dt)`. -/
theorem eLpNorm_comp_exp (f : ℝ → E) :
    eLpNorm f 2 (volume.restrict (Set.Ioi (0 : ℝ)))
      = eLpNorm (fun t => Real.exp (t / 2) • f (Real.exp t)) 2 volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [lintegral_norm_sq_comp_exp f]

/-- The inverse substitution: `(U⁻¹ h)(x) = x^{-1/2} h (log x)` also preserves the squared
`L²` integral, from `L²(ℝ)` back to `L²(0, ∞)`. -/
theorem mellin_log_unitary_symm (h : ℝ → E) :
    ∫ x in Set.Ioi (0 : ℝ), ‖(x : ℝ) ^ (-(1 : ℝ) / 2) • h (Real.log x)‖ ^ 2
      = ∫ t : ℝ, ‖h t‖ ^ 2 := by
  rw [mellin_log_unitary (fun x => (x : ℝ) ^ (-(1 : ℝ) / 2) • h (Real.log x))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hlog : Real.log (Real.exp t) = t := Real.log_exp t
  have hrpow : (Real.exp t) ^ (-(1 : ℝ) / 2) = Real.exp (-(t / 2)) := by
    rw [← Real.exp_mul]; ring_nf
  simp only [hlog, hrpow, smul_smul, ← Real.exp_add]
  norm_num

/-- The exponential map pushes the weighted Lebesgue measure `e^t dt` on `ℝ` forward to
Lebesgue measure on `(0, ∞)`. This is the measure-theoretic form of the substitution `x = e^t`. -/
theorem measurePreserving_exp_withDensity :
    MeasurePreserving Real.exp
      (volume.withDensity (fun t : ℝ => ENNReal.ofReal (Real.exp t)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  refine ⟨Real.measurable_exp, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply Real.measurable_exp hs, withDensity_apply _ (Real.measurable_exp hs),
    Measure.restrict_apply hs]
  have hcov := lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
    (s := univ) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (s.indicator 1)
  rw [exp_image_univ, setLIntegral_univ] at hcov
  have hleft : ∫⁻ x in Set.Ioi (0 : ℝ), s.indicator 1 x = volume (s ∩ Set.Ioi (0 : ℝ)) := by
    rw [lintegral_indicator hs]
    simp [Measure.restrict_apply hs]
  have hright : ∫⁻ x : ℝ, ENNReal.ofReal |Real.exp x| * s.indicator 1 (Real.exp x)
      = ∫⁻ a in Real.exp ⁻¹' s, ENNReal.ofReal (Real.exp a) := by
    rw [← lintegral_indicator (Real.measurable_exp hs)]
    refine lintegral_congr fun x => ?_
    by_cases hx : Real.exp x ∈ s <;>
      simp [hx, abs_of_pos (Real.exp_pos x), Set.mem_preimage]
  rw [← hright, ← hcov, hleft]

/-- Pointwise left inverse: applying `U` and then `U⁻¹` recovers `f` on `(0, ∞)`. -/
theorem mellin_log_inv_apply (f : ℝ → E) {x : ℝ} (hx : 0 < x) :
    (x : ℝ) ^ (-(1 : ℝ) / 2) •
        (Real.exp (Real.log x / 2) • f (Real.exp (Real.log x))) = f x := by
  have h1 : Real.exp (Real.log x / 2) = x ^ ((1 : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos hx]; ring_nf
  rw [Real.exp_log hx, h1, smul_smul, ← Real.rpow_add hx]
  norm_num

/-- Pointwise right inverse: applying `U⁻¹` and then `U` recovers `h` on `ℝ`. -/
theorem mellin_log_apply_inv (h : ℝ → E) (t : ℝ) :
    Real.exp (t / 2) •
        ((Real.exp t : ℝ) ^ (-(1 : ℝ) / 2) • h (Real.log (Real.exp t))) = h t := by
  have hrpow : (Real.exp t) ^ (-(1 : ℝ) / 2) = Real.exp (-(t / 2)) := by
    rw [← Real.exp_mul]; ring_nf
  rw [Real.log_exp, hrpow, smul_smul, ← Real.exp_add]
  norm_num

end DilationGenerator
end Brockian

