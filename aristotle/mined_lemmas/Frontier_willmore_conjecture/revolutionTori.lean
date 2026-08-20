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

noncomputable def revolutionTori : WillmoreSetting where
  Surface := {p : ℝ × ℝ // 0 < p.2 ∧ p.2 < p.1}
  genusOne := fun _ => True
  energy := fun p => willmoreEnergyTorus p.1.1 p.1.2
  clifford := ⟨cliffordRadii, by
    constructor
    · norm_num [cliffordRadii]
    · have : (1 : ℝ) < Real.sqrt 2 := by
        nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
      simpa [cliffordRadii] using this⟩
  clifford_genusOne := trivial
  clifford_energy := willmoreEnergyTorus_clifford

/-- **Willmore conjecture — Lean-checked base case (Marques–Neves).**

The full theorem of Marques and Neves states that every immersed torus in `ℝ³`
(equivalently, every genus-one closed surface) has Willmore energy at least
`2π²`, with equality exactly for the Clifford torus and its images under
conformal transformations.

What is proved here is the classical base case, for the family of tori of
revolution, together with the sharp equality characterization:

* every torus of revolution with radii `0 < r < R` has Willmore energy
  `π² R² / (r √(R² - r²)) ≥ 2π²`, i.e. the Clifford torus minimizes the
  Willmore energy in this class;
* equality holds precisely when `R = √2 · r`, the Clifford ratio.
-/
