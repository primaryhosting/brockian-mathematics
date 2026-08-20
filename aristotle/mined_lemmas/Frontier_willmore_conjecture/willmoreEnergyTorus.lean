/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
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

namespace Frontier

/-!
## The Willmore energy of a torus of revolution

For the torus of revolution in `ℝ³` obtained by revolving a circle of radius `r`
around an axis lying at distance `R > r` from its centre, the two principal
curvatures at the point of the tube at angle `θ` are

  `κ₁ = 1 / r`  and  `κ₂ = cos θ / (R + r cos θ)`,

the mean curvature is `H = (κ₁ + κ₂) / 2`, and the area element is
`r (R + r cos θ) dθ dφ`.  Integrating gives the classical closed formula

  `W(R, r) = ∫ H² dA = π² R² / (r √(R² - r²))`.

We take this closed formula as the definition of the Willmore energy of the
torus of revolution with radii `R > r > 0`; `willmoreEnergyTorus` below.
-/

/-- The Willmore energy `∫ H² dA` of the torus of revolution in `ℝ³` with
tube radius `r` and centre-circle radius `R` (meaningful for `0 < r < R`),
given by the classical closed formula `π² R² / (r √(R² - r²))`. -/

noncomputable def willmoreEnergyTorus (R r : ℝ) : ℝ :=
  Real.pi ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2))

/-- The *Clifford torus*, viewed as a torus of revolution in `ℝ³` via
stereographic projection from `S³`, is the one with ratio `R / r = √2`. -/
