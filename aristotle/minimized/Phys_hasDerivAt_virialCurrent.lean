import Mathlib
/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
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

open MeasureTheory Filter Topology

/-- The auxiliary ("virial current") function
`F x = c * (x * ψ'(x)^2 + ψ(x) * ψ'(x)) - x * (V x - E) * ψ x ^ 2`
attached to a solution of the stationary Schrödinger equation
`-c * ψ'' + V ψ = E ψ` (here `c = ℏ²/2m`). -/

noncomputable def virialCurrent (c E : ℝ) (psi dpsi V : ℝ → ℝ) : ℝ → ℝ :=
  fun x => c * (x * dpsi x ^ 2 + psi x * dpsi x) - x * (V x - E) * psi x ^ 2

/-- **Pointwise virial identity.**  If `psi` solves the stationary Schrödinger equation
`c * psi'' = (V - E) * psi` (i.e. `-c ψ'' + V ψ = E ψ`), then the virial current has
derivative `2 c (ψ')² - x V'(x) ψ(x)²`, i.e. exactly `2·(kinetic density) - (virial density)`. -/
