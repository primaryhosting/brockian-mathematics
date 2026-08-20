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

namespace CS

/-- **Knaster–Tarski**: a monotone map on a complete lattice has a least fixed point. -/

theorem knaster_tarski {α : Type*} [CompleteLattice α] (f : α → α) (hf : Monotone f) :
    ∃ a : α, f a = a ∧ ∀ b : α, f b = b → a ≤ b := by
  set S : Set α := {x : α | f x ≤ x}
  refine ⟨sInf S, ?_, ?_⟩
  · have hle : f (sInf S) ≤ sInf S := by
      refine le_sInf ?_
      intro x hx
      exact le_trans (hf (sInf_le hx)) hx
    refine le_antisymm hle ?_
    exact sInf_le (show f (f (sInf S)) ≤ f (sInf S) from hf hle)
  · intro b hb
    exact sInf_le (show f b ≤ b from le_of_eq hb)

end CS

#print axioms CS.knaster_tarski

