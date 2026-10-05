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

universe u

/-- **Zermelo's well-ordering theorem**: every type admits a well-order, i.e. a relation
which is trichotomous, transitive and well-founded (`IsWellOrder`). -/
theorem wellordering (α : Type u) : Nonempty { r : α → α → Prop // IsWellOrder α r } :=
  ⟨⟨WellOrderingRel, inferInstance⟩⟩

/-- A companion form: every type carries a linear order whose `<` relation is well-founded. -/
theorem exists_linearOrder_wellFoundedLT (α : Type u) :
    Nonempty { o : LinearOrder α // @WellFoundedLT α o.toLT } := by
  obtain ⟨r, hr⟩ := wellordering α
  refine ⟨⟨@IsWellOrder.linearOrder α r hr, ?_⟩⟩
  exact ⟨hr.wf⟩

end SetTheory

