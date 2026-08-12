import Mathlib

/-!
# Policy access model

A minimal access-control model: a principal `c : P` can access a resource `r : R`
when `r` is in `c`'s scope, or `c` is privileged, or `r` is unowned.
-/

namespace PCA

section
variable {P R : Type}

/-- `c` can access `r` if `r` is in scope for `c`, or `c` is privileged,
or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Removing the "unowned" disjunct refines access: the tightened policy
(with no unowned resources) allows a subset of what the original policy allows. -/
theorem tightening_refines (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) :
    canAccess inScope isPriv (fun _ => False) c r →
      canAccess inScope isPriv isUnowned c r := by
  rintro (h | h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact h.elim

end

end PCA

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

