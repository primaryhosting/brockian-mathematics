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
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`countingFunction S t` is the number of points of `S` that are `≤ t`
(with the convention `ncard = 0` for infinite sets). -/

lemma natRange_inter_Iic_subset (t : ℝ) :
    (Set.range ((↑) : ℕ → ℝ) ∩ Set.Iic t) ⊆ ((↑) : ℕ → ℝ) '' (Set.Iic ⌊t⌋₊) := by
  rintro x ⟨⟨n, rfl⟩, hn⟩
  refine ⟨n, ?_, rfl⟩
  have ht : 0 ≤ t := le_trans (Nat.cast_nonneg n) hn
  exact (Nat.le_floor_iff ht).mpr hn

