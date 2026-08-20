/-
# M 2 At One Assembly
Category: C Integral
Target: Zeta23Scaffold.m2_at_one_assembly
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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Scaffold

/-- The (normalized) sine kernel profile `S u = sin (π u) / (π u)`. -/
noncomputable def S (u : ℝ) : ℝ := Real.sin (Real.pi * u) / (Real.pi * u)

/--
Conditional assembly of the second moment of the sine-kernel Gram matrix at one:

`m₂(1) = 1 + ∫ S² - ∫ S⁴ = 4/3`,

given the two sinc-integral targets `∫ S² = 1` and `∫ S⁴ = 2/3` as explicit hypotheses.

This fixes, in Lean, the exact shape of the second-moment formula; the pair-correlation
derivation (`1 - S(u)²` for the sine process) is unformalized probability and is *not*
claimed here.
-/
theorem m2_at_one_assembly
    (hS2 : ∫ u : ℝ, (S u) ^ 2 = 1)
    (hS4 : ∫ u : ℝ, (S u) ^ 4 = 2 / 3) :
    1 + ((∫ u : ℝ, (S u) ^ 2) - (∫ u : ℝ, (S u) ^ 4)) = 4 / 3 := by
  rw [hS2, hS4]
  norm_num

end Zeta23Scaffold

