/-
# M 2 At One Assembly
Category: C Integral
Target: Zeta23Scaffold.m2_at_one_assembly
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The (normalized) sine kernel `S u = sin (π u) / (π u)`. -/
noncomputable def S (u : ℝ) : ℝ := Real.sin (Real.pi * u) / (Real.pi * u)

/--
Conditional assembly of the second moment at one for the sine process.

Given the two sinc-integral targets
`∫ S(u)^2 du = 1` and `∫ S(u)^4 du = 2/3`
(stated as explicit hypotheses, never as axioms), the second-moment formula
`m₂(1) = 1 + ∫ S² - ∫ S⁴` evaluates to `4/3`.

The pair-correlation derivation `1 - S(u)^2` behind the formula is unformalized
probability and is deliberately out of scope here; this statement only pins the
exact shape of the arithmetic assembly.
-/
theorem m2_at_one_assembly
    (hS2 : ∫ u : ℝ, (S u) ^ 2 = 1)
    (hS4 : ∫ u : ℝ, (S u) ^ 4 = 2 / 3) :
    1 + ((∫ u : ℝ, (S u) ^ 2) - (∫ u : ℝ, (S u) ^ 4)) = 4 / 3 := by
  rw [hS2, hS4]
  norm_num

end Zeta23Scaffold

