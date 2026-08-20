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

open Filter Topology Set

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`counting S Λ` is the number of points of `S` that are `≤ Λ`. -/

theorem discreteSpectrum_natSpec : DiscreteSpectrum natSpec := by
  intro Λ
  rcases le_or_gt 0 Λ with hΛ | hΛ
  · rw [natSpec_inter_Iic hΛ]
    exact (Set.finite_Iic _).image _
  · apply Set.Finite.subset Set.finite_empty
    rintro x ⟨⟨n, rfl⟩, hn⟩
    simp only [Set.mem_Iic] at hn
    exact absurd hn (by push_neg; linarith [Nat.cast_nonneg (α := ℝ) n])

