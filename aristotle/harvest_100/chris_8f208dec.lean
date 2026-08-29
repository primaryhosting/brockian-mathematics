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

/-- The substitution `x = exp t` maps `ℝ` bijectively onto `(0, ∞)`. -/
theorem image_exp_univ : Real.exp '' (univ : Set ℝ) = Ioi (0 : ℝ) := by
  rw [Set.image_univ, Real.range_exp]

/-- Change of variables `x = exp t` for the Lebesgue (Bochner) integral of an arbitrary
function on `(0, ∞)`: no integrability hypothesis is needed, since both sides are defined
to be `0` when the integrand fails to be integrable. -/
theorem integral_Ioi_eq_integral_exp_smul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : ℝ → F) :
    ∫ x in Ioi (0 : ℝ), g x = ∫ t : ℝ, Real.exp t • g (Real.exp t) := by
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := (univ : Set ℝ)) (f := Real.exp) (f' := Real.exp) (g := g)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (Real.exp_injective.injOn)
  rw [image_exp_univ] at h
  rw [h, MeasureTheory.Measure.restrict_univ]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [abs_of_pos (Real.exp_pos t)]

/-- **Mellin logarithmic substitution is norm preserving.**

The map `U : f ↦ (fun t => Real.exp (t / 2) • f (Real.exp t))`, induced by the substitution
`x = e^t`, carries the `L²`-norm on `(0, ∞)` to the `L²`-norm on `ℝ`:
`∫_{x > 0} ‖f x‖² = ∫_{t ∈ ℝ} ‖e^{t/2} • f (e^t)‖²`.

This is the analytic heart of the unitarity of `U : L²(0,∞) ≃ L²(ℝ)`; it holds for every
function `f`, with no integrability or measurability hypothesis. -/
theorem mellin_log_unitary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2
      = ∫ t : ℝ, ‖Real.exp (t / 2) • f (Real.exp t)‖ ^ 2 := by
  rw [integral_Ioi_eq_integral_exp_smul (fun x => ‖f x‖ ^ 2)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  have h2 : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
    rw [← Real.exp_add]; ring_nf
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
    smul_eq_mul, ← h2]
  ring

/-- The inverse map `h ↦ (fun x => x⁻¹ ^ (1/2 : ℝ) • h (Real.log x))` undoes `U` on `(0, ∞)`. -/
theorem mellin_log_inverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) {x : ℝ} (hx : 0 < x) :
    (x ^ (-(1 : ℝ) / 2) * Real.exp (Real.log x / 2)) • f (Real.exp (Real.log x)) = f x := by
  rw [Real.exp_log hx]
  have h1 : Real.exp (Real.log x / 2) = x ^ ((1 : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos hx]
    ring_nf
  rw [h1, ← Real.rpow_add hx]
  norm_num

end DilationGenerator

end Brockian

