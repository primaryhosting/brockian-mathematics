import Mathlib

/-!
# Sumset Lower Bound
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.sumset_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace AdditiveComb

open Finset Pointwise

/-- The translate `A + {min B}` and the translate `{max A} + B` meet in exactly one point,
namely `max A + min B`. -/

theorem sumset_lower_bound (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card - 1 ≤ (A + B).card := by
  have key := inter_translates_eq_singleton A B hA hB
  have hsub : (A + {B.min' hB}) ∪ ({A.max' hA} + B) ⊆ A + B :=
    union_subset (add_subset_add_left <| singleton_subset_iff.2 <| min'_mem _ _) <|
      add_subset_add_right <| singleton_subset_iff.2 <| max'_mem _ _
  have hcards : (A + {B.min' hB}).card = A.card := card_add_singleton _ _
  have hcardt : ({A.max' hA} + B).card = B.card := card_singleton_add _ _
  have hunion := card_union_add_card_inter (A + {B.min' hB}) ({A.max' hA} + B)
  rw [key, hcards, hcardt, card_singleton] at hunion
  have := card_le_card hsub
  omega

end AdditiveComb

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

