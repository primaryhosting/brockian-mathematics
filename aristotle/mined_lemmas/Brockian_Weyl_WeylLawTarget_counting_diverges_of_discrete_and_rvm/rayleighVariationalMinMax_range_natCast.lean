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

import Mathlib

/-!
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`counting S T` is the number of spectral points that are `≤ T`. -/

theorem rayleighVariationalMinMax_range_natCast :
    RayleighVariationalMinMax (Set.range (fun n : ℕ => (n : ℝ))) :=
  Set.infinite_range_of_injective (fun a b h => by exact_mod_cast h)

/-- Both hypotheses of `counting_diverges_of_discrete_and_rvm` are simultaneously
satisfiable, so the theorem is not vacuous. -/
example : Tendsto (counting (Set.range (fun n : ℕ => (n : ℝ)))) atTop atTop :=
  counting_diverges_of_discrete_and_rvm _ discreteSpectrum_range_natCast
    rayleighVariationalMinMax_range_natCast

end Brockian.Weyl.WeylLawTarget

