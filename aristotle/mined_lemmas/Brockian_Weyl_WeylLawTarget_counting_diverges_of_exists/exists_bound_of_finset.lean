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
# Counting Diverges Of Exists
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Counting Diverges Of Exists
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Brockian.Weyl.WeylLawTarget

open Filter Set

/-- The eigenvalue counting function of a family of eigenvalues `lam : ι → ℝ`:
`counting lam t` is the number of indices `i` with `lam i ≤ t`. -/

theorem exists_bound_of_finset {ι : Type*} (lam : ι → ℝ) (s : Finset ι) :
    ∃ T : ℝ, ∀ i ∈ s, lam i ≤ T := by
  obtain ⟨T, hT⟩ := (s.finite_toSet.image lam).bddAbove
  exact ⟨T, fun i hi => hT ⟨i, by simpa using hi, rfl⟩⟩

/-- **Weyl law counting divergence.**
If there exist infinitely many eigenstates (`Infinite ι`) and every eigenvalue
sublevel set is finite, then the eigenvalue counting function diverges to `+∞`. -/
