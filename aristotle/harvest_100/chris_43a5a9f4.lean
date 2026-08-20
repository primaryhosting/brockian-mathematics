import Mathlib

/-!
# Knaster Tarski
Category: Computer Science
Target: CS.knaster_tarski
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

namespace CS

/-- **Knaster–Tarski**: a monotone map `f` on a complete lattice has a least fixed point,
namely `sInf {x | f x ≤ x}`. -/
theorem knaster_tarski {α : Type*} [CompleteLattice α] (f : α → α) (hf : Monotone f) :
    ∃ a : α, f a = a ∧ ∀ b : α, f b = b → a ≤ b := by
  classical
  set S : Set α := {x : α | f x ≤ x} with hS
  refine ⟨sInf S, ?_, ?_⟩
  · have hle : f (sInf S) ≤ sInf S := by
      refine le_sInf ?_
      intro b hb
      exact le_trans (hf (sInf_le hb)) hb
    refine le_antisymm hle ?_
    exact sInf_le (show f (f (sInf S)) ≤ f (sInf S) from hf hle)
  · intro b hb
    exact sInf_le (le_of_eq hb)

end CS

