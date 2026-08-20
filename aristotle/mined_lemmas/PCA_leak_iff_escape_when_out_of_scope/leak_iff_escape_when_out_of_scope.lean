/-
# Leak Iff Escape When Out Of Scope
Category: Proof-Carrying Apps (Lean)
Target: PCA.leak_iff_escape_when_out_of_scope
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

namespace PCA

section

variable {P R : Type}

/-- Access is granted when the capability is in scope for the resource, or one of the
two "escape hatches" fires: the capability is privileged, or the resource is unowned. -/

theorem leak_iff_escape_when_out_of_scope
    (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) (h : ¬ inScope c r) :
    canAccess inScope isPriv isUnowned c r ↔ (isPriv c ∨ isUnowned r) :=
  -- `canAccess` unfolds to a disjunction whose first disjunct is refuted by `h`;
  -- this is Mathlib's `or_iff_right`.
  or_iff_right h

end

end PCA

