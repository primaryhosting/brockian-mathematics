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

/-- **Knaster–Tarski**: a monotone map on a complete lattice has a least fixed point.
That is, there is an `a` with `f a = a` which is below every fixed point of `f`.
The witness is `OrderHom.lfp ⟨f, hf⟩ = sInf {a | f a ≤ a}`; the key Mathlib lemmas are
`OrderHom.map_lfp` and `OrderHom.lfp_le`. -/
theorem knaster_tarski {α : Type*} [CompleteLattice α] (f : α → α) (hf : Monotone f) :
    ∃ a : α, f a = a ∧ ∀ b : α, f b = b → a ≤ b := by
  refine ⟨OrderHom.lfp ⟨f, hf⟩, OrderHom.map_lfp ⟨f, hf⟩, fun b hb => ?_⟩
  exact OrderHom.lfp_le _ hb.le

end CS

