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

set_option autoImplicit false

namespace Brockian.Weyl.WeylLawTarget

open Filter Set

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`counting S t` is the number of spectral points `≤ t`. -/

theorem discreteSpectrum_range_of_tendsto {lam : ℕ → ℝ}
    (h : Filter.Tendsto lam Filter.atTop Filter.atTop) :
    DiscreteSpectrum (Set.range lam) := by
  intro t
  obtain ⟨N, hN⟩ := (h.eventually_gt_atTop t).exists_forall_of_atTop
  have hsub : Set.range lam ∩ Set.Iic t ⊆ lam '' (Set.Iio N) := by
    rintro x ⟨⟨n, rfl⟩, hx⟩
    exact ⟨n, by
      simpa using not_le.mp fun hn => absurd hx (not_le.mpr (hN n hn)), rfl⟩
  exact Set.Finite.subset ((Set.finite_Iio N).image lam) hsub

/-- If an eigenvalue sequence `lam` tends to `+∞`, its range satisfies the RVM condition. -/
