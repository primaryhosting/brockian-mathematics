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

lemma countingFunction_natRange (t : ℝ) (ht : 0 ≤ t) :
    countingFunction (Set.range ((↑) : ℕ → ℝ)) t = ⌊t⌋₊ + 1 := by
  have hset : (Set.range ((↑) : ℕ → ℝ) ∩ Set.Iic t) = ((↑) : ℕ → ℝ) '' (Set.Iic ⌊t⌋₊) := by
    refine Set.Subset.antisymm (natRange_inter_Iic_subset t) ?_
    rintro x ⟨n, hn, rfl⟩
    exact ⟨⟨n, rfl⟩, (Nat.le_floor_iff ht).mp hn⟩
  have hIic : (Set.Iic ⌊t⌋₊) = ((Finset.Iic ⌊t⌋₊ : Finset ℕ) : Set ℕ) := by simp
  rw [countingFunction, hset, Set.ncard_image_of_injective _ Nat.cast_injective, hIic,
    Set.ncard_coe_finset]
  simp

/-- The hypotheses of the main theorem are not vacuous: the spectrum `ℕ ⊆ ℝ` is discrete and
matches the Weyl law in dimension `2` with leading constant `1`. -/
