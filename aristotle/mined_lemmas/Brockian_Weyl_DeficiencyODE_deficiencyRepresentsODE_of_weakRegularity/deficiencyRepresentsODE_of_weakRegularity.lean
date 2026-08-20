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

theorem deficiencyRepresentsODE_of_weakRegularity {q : ℝ → ℝ} (hq : Continuous q) (z : ℂ) :
    deficiencySet q z = odeSolutionSet q z := by
  ext u
  constructor
  · rintro ⟨hL2, hweak⟩
    exact ⟨hL2, weakRegularity hq (hL2.locallyIntegrable one_le_two) hweak⟩
  · rintro ⟨hL2, v, hv, hae⟩
    exact ⟨hL2, (WeakSolution.of_classical hq hv).congr_ae hae.symm⟩

end Brockian.Weyl.DeficiencyODE

import Mathlib

/-!
# Test functions and weak derivatives on the line

This file develops the small amount of one-dimensional distribution theory needed for the
regularity theory of Sturm–Liouville operators:

* `Brockian.Weyl.IsTestFunction`: smooth, compactly supported real functions on `ℝ`;
* integration by parts against a test function
  (`Brockian.Weyl.integral_deriv_testFunction_mul` for everywhere differentiable functions,
  `Brockian.Weyl.integral_deriv_testFunction_mul_primitive` for primitives of locally
  integrable functions);
* the du Bois-Reymond lemmas `Brockian.Weyl.ae_const_of_weak_deriv_eq_zero` and
  `Brockian.Weyl.ae_affine_of_weak_second_deriv_eq_zero`, saying that a locally integrable
  function whose first (resp. second) distributional derivative vanishes is almost
  everywhere constant (resp. affine).
-/

open MeasureTheory

namespace Brockian.Weyl

/-- A (real valued) test function on the line: smooth with compact support. -/
