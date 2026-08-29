import Mathlib
/-!
# Wellordering
Category: Frontier Wave 2 (deeper machinery)
Target: SetTheory.wellordering
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace SetTheory

/-- **Zermelo's well-ordering theorem**: every type admits a well-order, i.e. there is a
relation `r` on `α` which is a linear order (trichotomous and transitive) and well-founded. -/

theorem wellordering_linearOrder (α : Type*) :
    ∃ _ : LinearOrder α, WellFoundedLT α := by
  classical
  obtain ⟨r, hr⟩ := wellordering α
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

