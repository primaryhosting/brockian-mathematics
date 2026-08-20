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
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `Mono c col S` says that the finite set `S` is monochromatic of colour `col`
for the edge-colouring `c` : every pair of distinct vertices of `S` gets colour `col`. -/

theorem even_sum_adj_card (A : V → V → Prop) [DecidableRel A]
    (hs : ∀ x y, A x y → A y x) (hi : ∀ x, ¬ A x x) (T : Finset V) :
    Even (∑ v ∈ T, (T.filter (A v)).card) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
      rw [Finset.sum_insert ha]
      have h1 : ((insert a T).filter (A a)) = T.filter (A a) := by
        rw [Finset.filter_insert, if_neg (hi a)]
      have h2 : ∀ v ∈ T, ((insert a T).filter (A v)).card
          = (T.filter (A v)).card + (if A v a then 1 else 0) := by
        intro v hv
        rw [Finset.filter_insert]
        by_cases h : A v a
        · rw [if_pos h, if_pos h,
            Finset.card_insert_of_notMem (fun hmem => ha (Finset.mem_filter.mp hmem).1)]
        · rw [if_neg h, if_neg h, add_zero]
      rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, h1]
      have h3 : (∑ v ∈ T, if A v a then 1 else 0) = (T.filter (A a)).card := by
        rw [Finset.card_filter]
        refine Finset.sum_congr rfl ?_
        intro x hx
        by_cases h : A a x
        · rw [if_pos (hs a x h), if_pos h]
        · rw [if_neg (fun hax => h (hs x a hax)), if_neg h]
      rw [h3]
      obtain ⟨m, hm⟩ := ih
      exact ⟨m + (T.filter (A a)).card, by omega⟩

/-- `R(3,3) ≤ 6`: with no red triangle, any 6 vertices contain a blue triangle. -/
