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

/-!
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian.Weyl.WeylLawTarget

open Filter Set

/-- The spectral counting function of a set `S ⊆ ℝ` of eigenvalues:
`spectralCounting S T` is the number of elements of `S` that are `≤ T`. -/

theorem spectralCounting_mono {S : Set ℝ} (hdisc : DiscreteSpectrum S) :
    Monotone (spectralCounting S) := by
  intro T₁ T₂ hT
  exact Set.ncard_le_ncard (inter_subset_inter_right _ (Set.Iic_subset_Iic.mpr hT)) (hdisc T₂)

/-- If the spectrum below any level is finite and the spectrum is infinite, then for
every `n` there is a level beyond which the counting function is at least `n`. -/
