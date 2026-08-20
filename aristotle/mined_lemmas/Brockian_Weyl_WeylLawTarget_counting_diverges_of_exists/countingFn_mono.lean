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

theorem countingFn_mono (S : Set ℝ) (hloc : ∀ t : ℝ, {x ∈ S | x ≤ t}.Finite) :
    Monotone (countingFn S) := by
  intro s t hst
  refine Set.ncard_le_ncard ?_ (hloc t)
  rintro x ⟨hxS, hxs⟩
  exact ⟨hxS, hxs.trans hst⟩

/-- If a finite set `F` of eigenvalues sits inside `S`, then the counting function is at
least `F.card` from the maximum of `F` on. -/
