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

/-
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Complex
open scoped Convolution

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Test functions and the minimal Schrödinger expression -/

/-- A test function on the line: smooth with compact support. -/

theorem odeDeficiencyHypothesis_holds (V₀ : ℝ) : OdeDeficiencyHypothesis V₀ :=
  fun _ hz _ hu hweak => weak_solution_eq_zero V₀ hz hu hweak

/-! ## Essential self-adjointness -/

/-- **Essential self-adjointness of the minimal Schrödinger operator with constant potential.**

The minimal operator is `τ f = -f'' + V₀ f` acting on smooth compactly supported functions,
viewed as a densely defined operator on `L²(ℝ)`. The theorem states the two halves of the
basic criterion for essential self-adjointness:

* `τ` is symmetric on test functions;
* for every non-real `z`, the range of `τ - z` on test functions is dense in `L²(ℝ)`
  (equivalently, both deficiency spaces are trivial).

The ODE input that used to be assumed — that for non-real spectral parameter no nonzero
`L²` function solves `-u'' + V₀ u = z u` weakly — is discharged in
`Brockian.Weyl.SchrodingerMinimal.weak_solution_eq_zero`, so the statement is unconditional. -/
