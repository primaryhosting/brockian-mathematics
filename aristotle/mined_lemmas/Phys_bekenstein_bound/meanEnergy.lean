/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The (Gibbs–Shannon / von Neumann) entropy of a system whose microstates are indexed by `ι`
and occupied with probabilities `p`, measured in units of the Boltzmann constant `k`:
`S = -k ∑ᵢ pᵢ log pᵢ`. -/

noncomputable def meanEnergy {ι : Type*} [Fintype ι] (p Eℓ : ι → ℝ) : ℝ := ∑ i, p i * Eℓ i

/-- The Bekenstein bound `2 π k R E / (ℏ c)` on the entropy of a system of radius `R`
and energy `E`. -/
