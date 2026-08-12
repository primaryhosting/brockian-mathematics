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

/-- **Knaster–Tarski**: a monotone map `f` on a complete lattice has a least fixed point,
namely `sInf {x | f x ≤ x}`. -/
theorem knaster_tarski {α : Type*} [CompleteLattice α] (f : α → α) (hf : Monotone f) :
    ∃ a : α, IsLeast {x : α | f x = x} a := by
  refine ⟨sInf {x : α | f x ≤ x}, ?_, ?_⟩
  · -- `sInf {x | f x ≤ x}` is a fixed point
    set a : α := sInf {x : α | f x ≤ x}
    have hle : f a ≤ a := by
      refine le_sInf ?_
      intro b hb
      exact le_trans (hf (sInf_le hb)) hb
    have hge : a ≤ f a := sInf_le (hf hle)
    exact le_antisymm hle hge
  · -- and it is below every fixed point
    intro x hx
    exact sInf_le (le_of_eq hx)

end CS

