import Mathlib

/-!
# Conjugation To Momentum
Category: Gate1 Operator
Target: Brockian.DilationGenerator.conjugation_to_momentum
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

/-- The unitary `U` implementing the logarithmic substitution on the core:
`(U f) t = e^{t/2} f(e^t)`. -/

noncomputable def logSubst (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => Real.exp (t / 2) • f (Real.exp t)

/-- Derivative of the log-substituted function: for smooth `f`,
`(U f)'(t) = e^{t/2} ((1/2) f(e^t) + e^t f'(e^t))`. -/
