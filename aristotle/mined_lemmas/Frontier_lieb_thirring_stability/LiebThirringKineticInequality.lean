/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

open MeasureTheory

/-! ## The pointwise (Young) inequality underlying stability -/

/-- The Lieb–Thirring stability constant appearing in the bound
`Kc * a ^ (5/3) - t * a ≥ - ltConst Kc * t ^ (5/2)`. -/

def LiebThirringKineticInequality (Kc : ℝ) : Prop :=
  ∀ (N : ℕ) (ψ : Fin N → Space → ℂ), Admissible ψ →
    Kc * ∫ x, (density ψ x) ^ (5 / 3 : ℝ) ≤ ∑ i, kineticEnergy (ψ i)

/-- **Stability of matter, reduced to the Lieb–Thirring inequality.**

For a system of `N` fermions described by an orthonormal family `ψ` of one-particle wave
functions, whose interaction energy `V` with the nuclei (and among themselves) is bounded
below by `- b ∫ W ρ` for a nonnegative one-body potential `W` with `W ^ (5/2)` integrable
(this is the content of the electrostatic/Baxter inequality, with `W` the inverse distance
to the nearest nucleus suitably localized), the total energy satisfies the uniform lower
bound

`E = T + V ≥ - ltConst Kc * b ^ (5/2) * ∫ W ^ (5/2)`,

whose right-hand side does not depend on the number `N` of particles. Combined with a bound
`∫ W ^ (5/2) ≤ A * K` for `K` nuclei, this gives the linear-in-particle-number lower bound
that constitutes stability of matter. -/
