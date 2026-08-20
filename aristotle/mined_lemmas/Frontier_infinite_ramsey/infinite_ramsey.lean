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

namespace Frontier

section Ramsey

variable (c : ℕ → ℕ → Bool)

/-- The elements of `A` strictly above `a` receiving colour `b` (paired with `a`). -/

theorem infinite_ramsey (c : Finset ℕ → Bool) :
    ∃ S : Set ℕ, S.Infinite ∧ ∃ b : Bool, ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c {i, j} = b := by
  obtain ⟨S, hS, b, hb⟩ := infinite_ramsey_lt (fun i j => c {i, j})
  refine ⟨S, hS, b, ?_⟩
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hb i hi j hj h
  · have := hb j hj i hi h
    rwa [Finset.pair_comm] at this

end Frontier

#print axioms Frontier.infinite_ramsey
#print axioms Frontier.infinite_ramsey_lt

