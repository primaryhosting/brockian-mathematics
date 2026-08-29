import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The set of base points `x` of a translate of the shift `d` landing inside `S`,
i.e. `{x | x + d ∈ S}`. -/

theorem card_inter_add_card_univ_ge (A B : Finset G) :
    A.card + B.card ≤ (A ∩ B).card + Fintype.card G := by
  have h := Finset.card_inter_add_card_union A B
  have h2 : (A ∪ B).card ≤ Fintype.card G := by
    simpa using Finset.card_le_card (Finset.subset_univ (A ∪ B))
  omega

/-- For `k = 3`, the local constellation count is the cardinality of the intersection of the
three shifted preimages of `S`. -/
