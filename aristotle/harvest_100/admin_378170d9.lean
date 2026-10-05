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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian.DilationGenerator

open MeasureTheory Set

/-- Change of variables `x = exp t` for an arbitrary integrand on `(0, ∞)`:
`∫_{(0,∞)} g x dx = ∫_ℝ exp t • g (exp t) dt`. -/
theorem integral_Ioi_eq_integral_comp_exp {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (g : ℝ → F) :
    ∫ x in Ioi (0 : ℝ), g x = ∫ t : ℝ, Real.exp t • g (Real.exp t) := by
  have himg : Real.exp '' univ = Ioi (0 : ℝ) := by
    simp [Real.range_exp]
  have hkey :
      ∫ x in Real.exp '' univ, g x
        = ∫ t in (univ : Set ℝ), |Real.exp t| • g (Real.exp t) :=
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g
  rw [himg] at hkey
  rw [hkey, MeasureTheory.Measure.restrict_univ]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
    show |Real.exp t| • g (Real.exp t) = Real.exp t • g (Real.exp t)
    rw [abs_of_pos (Real.exp_pos t)])

/-- **Mellin log unitary.**  The substitution `x = eᵗ` turns the `L²`-integral of `f` on
`(0, ∞)` (with Lebesgue measure) into the `L²`-integral over `ℝ` of
`U f : t ↦ e^{t/2} • f (eᵗ)`.  In particular the map `f ↦ U f` is norm preserving,
which is the analytic content of the unitarity of the Mellin/logarithmic substitution
`L²(0,∞) ≃ L²(ℝ)`.  No integrability hypothesis is needed: the identity holds for every
`f`, both sides being simultaneously defined (or both undefined, hence `0`). -/
theorem mellin_log_unitary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 = ∫ t : ℝ, ‖Real.exp (t / 2) • f (Real.exp t)‖ ^ 2 := by
  rw [integral_Ioi_eq_integral_comp_exp (fun x => ‖f x‖ ^ 2)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show Real.exp t • ‖f (Real.exp t)‖ ^ 2 = ‖Real.exp (t / 2) • f (Real.exp t)‖ ^ 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, smul_eq_mul,
    sq (Real.exp (t / 2)), ← Real.exp_add]
  ring_nf

/-- The inverse substitution: for `h : ℝ → E`, the map `h ↦ (x ↦ x^{-1/2} • h (log x))`
sends the `L²`-integral over `ℝ` to the `L²`-integral over `(0, ∞)`. -/
theorem mellin_log_unitary_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ → E) :
    ∫ t : ℝ, ‖h t‖ ^ 2
      = ∫ x in Ioi (0 : ℝ), ‖(x ^ (-(1 : ℝ) / 2 : ℝ) : ℝ) • h (Real.log x)‖ ^ 2 := by
  have := mellin_log_unitary (E := E) (fun x => (x ^ (-(1 : ℝ) / 2 : ℝ) : ℝ) • h (Real.log x))
  rw [this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show ‖h t‖ ^ 2
      = ‖Real.exp (t / 2) • ((Real.exp t) ^ (-(1 : ℝ) / 2 : ℝ) : ℝ) • h (Real.log (Real.exp t))‖ ^ 2
  have hx : Real.exp (t / 2) * ((Real.exp t) ^ (-(1 : ℝ) / 2 : ℝ)) = 1 := by
    rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp, ← Real.exp_add,
      show t / 2 + t * (-(1 : ℝ) / 2) = 0 by ring, Real.exp_zero]
  rw [Real.log_exp, smul_smul, hx, one_smul]

end Brockian.DilationGenerator

