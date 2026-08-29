import Mathlib
/-!
# Tightening Refines
Category: Proof-Carrying Apps (Lean)
Target: PCA.tightening_refines
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA

section
variable {P R : Type}

/-- Access is granted when the capability is in scope, the capability is
privileged, or the resource is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Removing the "unowned" disjunct refines access: any access granted by the
tightened policy is also granted by the original policy. -/
theorem tightening_refines (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) :
    canAccess inScope isPriv (fun _ => False) c r →
      canAccess inScope isPriv isUnowned c r := by
  rintro (h | h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact absurd h not_false

end

end PCA

#print axioms PCA.tightening_refines

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

