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

open Filter
open scoped Topology

namespace Brockian.Weyl.WeylLawTarget

/-- The Weyl counting function of a set of eigenvalues `S ⊆ ℝ`:
`countingFn S t` is the number of elements of `S` that are `≤ t`. -/

theorem card_le_countingFn (S : Set ℝ) (hloc : ∀ t : ℝ, {x ∈ S | x ≤ t}.Finite)
    (F : Finset ℝ) (hFS : ↑F ⊆ S) {t : ℝ} (ht : ∀ x ∈ F, x ≤ t) :
    F.card ≤ countingFn S t := by
  have hsub : (↑F : Set ℝ) ⊆ {x ∈ S | x ≤ t} := by
    intro x hx
    exact ⟨hFS hx, ht x (by simpa using hx)⟩
  have := Set.ncard_le_ncard hsub (hloc t)
  simpa [countingFn, Set.ncard_coe_finset] using this

/-- **Weyl-law counting divergence.**  If the eigenvalue set `S ⊆ ℝ` has finite sublevel sets
(local finiteness / discreteness of the spectrum below any energy) and contains arbitrarily
large finite subsets (i.e. there exist arbitrarily many eigenvalues), then the counting
function `t ↦ #{x ∈ S | x ≤ t}` diverges to `+∞`.

This is the unconditional form: the conclusion is obtained from the mere existence
statement `hex`, with no further assumptions. -/
