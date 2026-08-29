/-
# Wellordering
Category: Frontier Wave 2 (deeper machinery)
Target: SetTheory.wellordering
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace SetTheory

/-- **Zermelo's well-ordering theorem**: every type carries a well-order.
Formally, for any type `α` the subtype of relations `r : α → α → Prop` satisfying
`IsWellOrder α r` is nonempty.  Recall that `IsWellOrder α r` packages together
trichotomy, transitivity and well-foundedness of `r`, so such an `r` is in particular
a strict linear order whose associated `≤` is a `LinearOrder` on `α`. -/

theorem exists_linearOrder_wellFounded (α : Type*) :
    ∃ _ : LinearOrder α, WellFounded ((· < ·) : α → α → Prop) := by
  obtain ⟨r, hr⟩ := wellordering α
  letI : LinearOrder α := linearOrderOfSTO r
  refine ⟨inferInstance, ?_⟩
  exact hr.wf

end SetTheory

