import Mathlib
/-!
# Wellordering
Category: Frontier Wave 2 (deeper machinery)
Target: SetTheory.wellordering
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace SetTheory

/-- **Zermelo's well-ordering theorem.** Every type admits a well-order: there exists a
relation `r` on `α` which is a well-order, i.e. a trichotomous, transitive, well-founded
relation (equivalently, a linear order on `α` whose strict order is well-founded). -/
theorem wellordering (α : Type*) : Nonempty { r : α → α → Prop // IsWellOrder α r } :=
  ⟨⟨WellOrderingRel, inferInstance⟩⟩

/-- Unpacked form of `SetTheory.wellordering`: every type carries a relation that is
trichotomous, transitive and well-founded. -/
theorem wellordering' (α : Type*) :
    ∃ r : α → α → Prop, Std.Trichotomous r ∧ IsTrans α r ∧ WellFounded r := by
  obtain ⟨r, hr⟩ := wellordering α
  exact ⟨r, hr.toTrichotomous, hr.toIsTrans, hr.wf⟩

/-- Every type admits a `LinearOrder` structure which is a well-order, i.e. whose strict
order `<` is well-founded. -/
theorem exists_wellOrder_linearOrder (α : Type*) :
    ∃ _ : LinearOrder α, WellFoundedLT α := by
  obtain ⟨r, hr⟩ := wellordering α
  letI : IsWellOrder α r := hr
  letI : DecidableRel r := Classical.decRel r
  exact ⟨linearOrderOfSTO r, ⟨hr.wf⟩⟩

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

