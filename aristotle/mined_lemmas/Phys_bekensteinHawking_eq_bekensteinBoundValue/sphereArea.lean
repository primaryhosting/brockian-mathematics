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

noncomputable def sphereArea (R : ℝ) : ℝ := 4 * Real.pi * R ^ 2

/-- **Key computation.** For a Schwarzschild black hole of energy `E`, whose horizon radius is
`R = 2 G E / c ^ 4`, the Bekenstein–Hawking entropy of the horizon is *exactly* the Bekenstein
bound value `2 π k R E / (ℏ c)`.  (This is the standard derivation: the gravitational constant
`G = R c ^ 4 / (2 E)` is eliminated using the Schwarzschild relation.) -/
