import Mathlib

/-!
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
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

namespace Phys

/-- The Bekenstein bound expression `2 π k R E / (ℏ c)`: the maximal entropy that can be
contained in a region of radius `R` enclosing total energy `E`. -/

theorem bekensteinHawking_eq_bekensteinBoundValue
    {k hbar c G R E : ℝ} (hhbar : hbar ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0)
    (hR : R = schwarzschildRadius G c E) :
    bekensteinHawkingEntropy k hbar c G (sphereArea R) = bekensteinBoundValue k hbar c R E := by
  subst hR
  unfold bekensteinHawkingEntropy bekensteinBoundValue sphereArea schwarzschildRadius
  field_simp

/-- **The Bekenstein bound.**

For a physical system of total energy `E` contained inside a sphere of radius `R`, the
entropy `S` satisfies
`S ≤ 2 π k R E / (ℏ c)`.

The physical input (Susskind's spherical-entropy argument / the generalized second law) is the
hypothesis `hS`: the entropy of the system does not exceed the Bekenstein–Hawking entropy
`k c ^ 3 A / (4 G ℏ)` of a black hole with the same energy, whose horizon `R` is the
Schwarzschild radius of that energy.  Given this, the bound in the stated form is an exact
consequence of the Schwarzschild relation `R = 2 G E / c ^ 4`. -/
