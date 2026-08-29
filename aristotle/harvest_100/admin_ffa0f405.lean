/-
# Wellordering
Category: Frontier Wave 2 (deeper machinery)
Target: SetTheory.wellordering
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace SetTheory

/-- **Zermelo's well-ordering theorem**: every type carries a well-order.
Formally, for any type `α` there exists a relation `r : α → α → Prop`
which is a well-order: it is trichotomous, transitive and well-founded,
and hence induces a linear order on `α`. -/
theorem wellordering (α : Type*) : Nonempty { r : α → α → Prop // IsWellOrder α r } :=
  ⟨⟨(WellOrderingRel : α → α → Prop), WellOrderingRel.isWellOrder⟩⟩

open Classical in
/-- The linear order on an arbitrary type `α` obtained from the well-order
`WellOrderingRel`. -/
noncomputable def wellOrderingLinearOrder (α : Type*) : LinearOrder α :=
  linearOrderOfSTO (WellOrderingRel : α → α → Prop)

/-- The order-theoretic form of the well-ordering theorem: every type admits a
linear order whose strict part is well-founded. -/
theorem exists_linearOrder_wellFoundedLT (α : Type*) :
    ∃ o : LinearOrder α, @WellFoundedLT α o.toLT :=
  ⟨wellOrderingLinearOrder α, by
    constructor
    exact (WellOrderingRel.isWellOrder (α := α)).wf⟩

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

