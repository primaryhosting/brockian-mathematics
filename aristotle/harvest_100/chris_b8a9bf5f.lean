/-
# Baire Category
Category: Pure Mathematics
Target: Math.baire_category
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


import Mathlib

/-!
# Baire Category
Category: Pure Mathematics
Target: Math.baire_category
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math

/-- **Baire category theorem.**  A nonempty complete metric space is not the union of a
countable family of nowhere dense sets: if every `f n` has closure with empty interior,
then `⋃ n, f n` cannot be all of `X`. -/
theorem baire_category {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {ι : Type*} [Countable ι] (f : ι → Set X)
    (hf : ∀ i, interior (closure (f i)) = ∅) :
    (⋃ i, f i) ≠ Set.univ := by
  intro hunion
  -- The closures cover `X` as well.
  have hcov : (Set.univ : Set X) ⊆ ⋃ i, closure (f i) := by
    rw [← hunion]
    exact Set.iUnion_mono fun i => subset_closure
  -- By Baire, some closure has nonempty interior.
  obtain ⟨i, x, hx⟩ :=
    nonempty_interior_of_iUnion_of_closed (fun i => isClosed_closure)
      (Set.eq_univ_of_univ_subset hcov)
  rw [hf i] at hx
  exact hx

/-- Restatement in terms of Mathlib's `IsNowhereDense`. -/
theorem baire_category' {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {ι : Type*} [Countable ι] (f : ι → Set X)
    (hf : ∀ i, IsNowhereDense (f i)) :
    (⋃ i, f i) ≠ Set.univ :=
  baire_category f hf

end Math

