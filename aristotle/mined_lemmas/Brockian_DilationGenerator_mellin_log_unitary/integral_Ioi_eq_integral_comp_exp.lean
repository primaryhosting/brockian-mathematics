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
