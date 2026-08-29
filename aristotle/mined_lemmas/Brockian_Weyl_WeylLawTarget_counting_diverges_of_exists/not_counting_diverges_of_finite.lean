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

theorem not_counting_diverges_of_finite {ι : Type*} [Finite ι] (lam : ι → ℝ) :
    ¬ Filter.Tendsto (counting lam) Filter.atTop Filter.atTop := by
  intro h
  have h' := (Filter.tendsto_atTop.1 h (Nat.card ι + 1)).exists
  obtain ⟨t, ht⟩ := h'
  exact absurd (ht.trans (counting_le_natCard lam t)) (by omega)

/-- Divergence of the counting function is *equivalent* to the existence of infinitely
many eigenstates, once all sublevel sets are finite. -/
