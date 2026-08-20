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

theorem integrable_mul {φ : ℝ → ℝ} (hφ : IsTestFunction φ) {v : ℝ → ℂ}
    (hv : LocallyIntegrable v volume) : Integrable (fun x => (φ x : ℂ) * v x) volume := by
  obtain ⟨C, hC⟩ := hφ.2.exists_bound_of_continuous hφ.continuous
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport φ) ?_ ?_
  · exact Integrable.bdd_mul (c := C) (hv.integrableOn_isCompact hφ.2)
      (Complex.continuous_ofReal.comp hφ.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa using hC x)
  · intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]

/-- The integral of the derivative of a test function vanishes. -/
