import Mathlib
/-!
# Wellordering
Category: Frontier Wave 2 (deeper machinery)
Target: SetTheory.wellordering
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace SetTheory

/-- **Zermelo's well-ordering theorem**: every type admits a well-order.

For any type `α` there exists a relation `r : α → α → Prop` which is a well-order
(`IsWellOrder α r`, i.e. `r` is trichotomous, transitive and well-founded).

This is exactly Mathlib's instance `IsWellOrder.subtype_nonempty`. -/

theorem exists_linearOrder_wellFounded (α : Type*) :
    ∃ _ : LinearOrder α, WellFounded ((· < ·) : α → α → Prop) := by
  obtain ⟨r, hr⟩ := wellordering α
  have : IsWellOrder α r := hr
  haveI : DecidableRel r := Classical.decRel r
  refine ⟨linearOrderOfSTO r, ?_⟩
  have hwf : WellFounded r := (isWellFounded_iff α r).1 inferInstance
  exact hwf

end SetTheory

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

