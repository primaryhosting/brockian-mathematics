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

/-
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Set

namespace Brockian.Weyl

/-- The (Weyl) eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`counting S T` is the number of spectral points that are `≤ T`. -/

theorem infinite_natCast_range : (Set.range (fun n : ℕ => (n : ℝ))).Infinite :=
  Set.infinite_range_of_injective fun a b h => by exact_mod_cast h

/-- Both hypotheses of `counting_diverges_of_discrete_and_rvm` hold for the model
spectrum `{0, 1, 2, …}`, so the theorem is not vacuous. -/
example : Filter.Tendsto (counting (Set.range (fun n : ℕ => (n : ℝ)))) Filter.atTop Filter.atTop :=
  WeylLawTarget.counting_diverges_of_discrete_and_rvm discreteSpectrum_natCast
    infinite_natCast_range

end Brockian.Weyl

