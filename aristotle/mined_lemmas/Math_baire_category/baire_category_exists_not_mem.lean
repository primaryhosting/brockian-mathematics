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

namespace Math

/-- **Baire category theorem** (complement form): a nonempty complete metric space is not the
union of a countable family of nowhere dense subsets.

Here `IsNowhereDense s` means `interior (closure s) = ∅`.  The nonemptiness hypothesis is
necessary: the empty space *is* the (empty) union of nowhere dense sets. -/

theorem baire_category_exists_not_mem {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (f : ℕ → Set X) (hf : ∀ n, interior (closure (f n)) = ∅) :
    ∃ x : X, ∀ n, x ∉ f n := by
  have h : (⋃ n, f n) ≠ (Set.univ : Set X) := baire_category f fun n => hf n
  obtain ⟨x, hx⟩ : ∃ x : X, x ∉ ⋃ n, f n := by
    by_contra hc
    exact h (Set.eq_univ_of_forall (by simpa using hc))
  exact ⟨x, fun n hn => hx (Set.mem_iUnion.2 ⟨n, hn⟩)⟩

end Math

#print axioms Math.baire_category
#print axioms Math.baire_category_exists_not_mem

