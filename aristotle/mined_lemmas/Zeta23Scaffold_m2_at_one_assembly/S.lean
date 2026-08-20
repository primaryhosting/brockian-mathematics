import Mathlib

/-!
# M 2 At One Assembly
Category: C Integral
Target: Zeta23Scaffold.m2_at_one_assembly
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


namespace Zeta23Scaffold

/-- The normalized sine kernel `S u = sin (π u) / (π u)`. -/

noncomputable def S (u : ℝ) : ℝ := Real.sin (Real.pi * u) / (Real.pi * u)

/-- Conditional assembly of the second moment of the sine process at one:
given the two sinc integrals `∫ S² = 1` and `∫ S⁴ = 2/3`, the second-moment
formula `m₂(1) = 1 + ∫ S² - ∫ S⁴` evaluates to `4/3`.
The two integral values are hypotheses, not axioms. -/
