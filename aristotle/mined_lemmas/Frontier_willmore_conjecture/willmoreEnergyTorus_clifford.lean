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

theorem willmoreEnergyTorus_clifford :
    willmoreEnergyTorus cliffordRadii.1 cliffordRadii.2 = 2 * Real.pi ^ 2 := by
  have h2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  simp only [cliffordRadii, willmoreEnergyTorus, h2]
  norm_num
  ring

/-!
## A schematic formalization of the general conjecture

Mathlib currently has no theory of mean curvature of immersed surfaces, so the
full Marques–Neves theorem cannot be stated verbatim.  The structure below
records the *shape* of the statement: a class of surfaces, a genus-one
predicate, a Willmore energy, and a distinguished Clifford torus of energy
`2π²`.  `MinimizedByClifford` is then the assertion that the Clifford torus
minimizes the Willmore energy in that class.
-/

/-- A schematic setting for the Willmore problem: a class of surfaces equipped
with a genus-one predicate, a Willmore energy functional, and a distinguished
"Clifford torus" of genus one whose energy is `2π²`. -/
structure WillmoreSetting where
  /-- The class of surfaces under consideration. -/
  Surface : Type
  /-- The predicate singling out the genus-one surfaces. -/
  genusOne : Surface → Prop
  /-- The Willmore energy `∫ H² dA`. -/
  energy : Surface → ℝ
  /-- The distinguished Clifford torus of the setting. -/
  clifford : Surface
  /-- The Clifford torus has genus one. -/
  clifford_genusOne : genusOne clifford
  /-- The Willmore energy of the Clifford torus is `2π²`. -/
  clifford_energy : energy clifford = 2 * Real.pi ^ 2

/-- The Willmore conjecture for a given setting: every genus-one surface has
Willmore energy at least that of the Clifford torus, namely `2π²`. -/
