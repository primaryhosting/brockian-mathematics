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

theorem discreteSpectrum_natCast : DiscreteSpectrum (Set.range (fun n : ℕ => (n : ℝ))) := by
  intro T
  apply Set.Finite.subset ((Set.finite_Icc 0 ⌊T⌋₊).image (fun n : ℕ => (n : ℝ)))
  rintro x ⟨⟨n, rfl⟩, hx⟩
  exact ⟨n, ⟨Nat.zero_le _, Nat.le_floor hx⟩, rfl⟩

/-- The spectrum `{0, 1, 2, …} ⊆ ℝ` is infinite. -/
