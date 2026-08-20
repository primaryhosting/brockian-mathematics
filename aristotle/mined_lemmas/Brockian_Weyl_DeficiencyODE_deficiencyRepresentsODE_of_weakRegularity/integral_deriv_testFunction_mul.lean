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

import Brockian.Weyl.WeakDerivative

/-!
# Weyl deficiency spaces are represented by solutions of the Schrödinger ODE

For a continuous potential `q : ℝ → ℝ` and a spectral parameter `z : ℂ`, consider the
formally symmetric differential expression `τ u = -u'' + q u` on the line.  The minimal
operator is the restriction of `τ` to test functions, and the deficiency space at `z`
consists of the `L²` functions `u` which satisfy `τ u = z u` *weakly*, i.e. in the sense
of distributions:

  `∫ u φ'' = ∫ (q - z) u φ`   for all real test functions `φ`.

The main result of this file, `deficiencyRepresentsODE_of_weakRegularity`, states that
this deficiency space coincides with the set of `L²` functions which agree almost
everywhere with a *classical* (twice differentiable) solution of the ODE
`-u'' + q u = z u`.

The nontrivial inclusion is a regularity statement — every weak solution is almost
everywhere a classical solution — which is proved here from scratch (`weakRegularity`)
from the du Bois-Reymond lemmas of `Brockian.Weyl.WeakDerivative`; consequently the final

theorem integral_deriv_testFunction_mul {F f : ℝ → ℂ} (hF : ∀ x, HasDerivAt F (f x) x)
    (hf : Continuous f) {ψ : ℝ → ℝ} (hψ : IsTestFunction ψ) :
    ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * F x = -∫ x : ℝ, (ψ x : ℂ) * f x := by
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun x => (hF x).continuousAt
  have hHd : ∀ x, HasDerivAt (fun y => (ψ y : ℂ) * F y)
      (((deriv ψ x : ℝ) : ℂ) * F x + (ψ x : ℂ) * f x) x := fun x =>
    (((hψ.differentiable x).hasDerivAt).ofReal_comp).mul (hF x)
  have hint1 : Integrable (fun x => ((deriv ψ x : ℝ) : ℂ) * F x) volume :=
    hψ.deriv'.integrable_mul hFc.locallyIntegrable
  have hint2 : Integrable (fun x => (ψ x : ℂ) * f x) volume :=
    hψ.integrable_mul hf.locallyIntegrable
  have h0 := MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable hHd (hint1.add hint2)
    (hψ.integrable_mul hFc.locallyIntegrable)
  rw [integral_add hint1 hint2] at h0
  exact eq_neg_of_add_eq_zero_left h0

/-! ### Integration by parts against a primitive -/

section Primitive

variable {ψ : ℝ → ℝ} {g : ℝ → ℂ}

/-- The kernel used in the Fubini argument below is integrable on the product. -/
