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

theorem natSpec_inter_Iic {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    natSpec ∩ Set.Iic Λ = (fun n : ℕ => (n : ℝ)) '' (Set.Iic ⌊Λ⌋₊) := by
  ext x
  simp only [natSpec, Set.mem_inter_iff, Set.mem_range, Set.mem_Iic, Set.mem_image]
  constructor
  · rintro ⟨⟨n, rfl⟩, hn⟩
    exact ⟨n, (Nat.le_floor_iff hΛ).mpr hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, rfl⟩, (Nat.le_floor_iff hΛ).mp hn⟩

