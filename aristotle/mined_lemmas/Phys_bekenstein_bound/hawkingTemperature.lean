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

/-- The Bekenstein bound value `2 π k R E / (ℏ c)`: the maximal entropy that can be
contained in a region of radius `R` enclosing total energy `E`. -/

noncomputable def hawkingTemperature (k hbar c G M : ℝ) : ℝ :=
  hbar * c ^ 3 / (8 * Real.pi * G * M * k)

/-- Bekenstein–Hawking entropy `k c³ A / (4 G ℏ)` of a Schwarzschild black hole of mass `M`,
written out with `A = 4 π (2GM/c²)²`, i.e. `4 π k G M² / (ℏ c)`. -/
