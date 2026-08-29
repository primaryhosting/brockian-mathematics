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

theorem counting_sq_diverges :
    DiscreteSpectrum (Set.range fun n : ℕ => (n : ℝ) ^ 2) ∧
      RVM (Set.range fun n : ℕ => (n : ℝ) ^ 2) ∧
      Filter.Tendsto (counting (Set.range fun n : ℕ => (n : ℝ) ^ 2))
        Filter.atTop Filter.atTop := by
  have h : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 2) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun n : ℕ => ?_) tendsto_natCast_atTop_atTop
    have hn : (n : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.le_self_pow two_ne_zero n)
    simpa using hn
  exact ⟨discreteSpectrum_range_of_tendsto h, rvm_range_of_tendsto h,
    counting_range_diverges_of_tendsto h⟩

end Brockian.Weyl.WeylLawTarget

