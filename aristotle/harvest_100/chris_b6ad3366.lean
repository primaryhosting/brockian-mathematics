import Mathlib

/-!
# Default Deny
Category: Proof-Carrying Apps (Lean)
Target: PCA.default_deny
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


namespace PCA

section
variable {P R : Type}

/-- A capability `c` may access resource `r` when `r` is in `c`'s scope, or `c` is
privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- With empty scope and no escape hatches, nothing is accessible. -/
theorem default_deny {inScope : P → R → Prop} {isPriv : P → Prop} {isUnowned : R → Prop}
    (hs : ∀ c r, ¬ inScope c r) (hp : ∀ c, ¬ isPriv c) (hu : ∀ r, ¬ isUnowned r)
    (c : P) (r : R) : ¬ canAccess inScope isPriv isUnowned c r := by
  rintro (h | h | h)
  · exact hs c r h
  · exact hp c h
  · exact hu r h

end

end PCA

#print axioms PCA.default_deny

