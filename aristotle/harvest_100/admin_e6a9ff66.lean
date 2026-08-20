/-
# Baire Category
Category: Pure Mathematics
Target: Math.baire_category
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Set

namespace Math

/-- **Baire category theorem**: a nonempty complete metric space is not the union of
countably many nowhere-dense sets. -/
theorem baire_category {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {ι : Type*} [Countable ι] (s : ι → Set X) (hs : ∀ i, IsNowhereDense (s i)) :
    ⋃ i, s i ≠ univ := by
  intro hcov
  -- Pass to closures: they are closed, still cover the space, and have empty interior.
  have hclosed : ∀ i, IsClosed (closure (s i)) := fun i => isClosed_closure
  have hcov' : ⋃ i, closure (s i) = univ :=
    eq_univ_of_subset (iUnion_mono fun i => subset_closure) hcov
  -- Baire (`nonempty_interior_of_iUnion_of_closed`) gives a set with nonempty interior.
  obtain ⟨i, hi⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcov'
  rw [hs i] at hi
  exact hi.ne_empty rfl

end Math

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

