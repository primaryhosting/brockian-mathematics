import Mathlib

namespace PCA

section PCA

variable {P R : Type}

/-- Access is granted if the resource is in the principal's scope, or the
principal is privileged, or the resource is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- With no privileged principals and no unowned resources, any granted access
is in-scope. -/
theorem no_escape_no_leak {isPriv : P → Prop} {isUnowned : R → Prop}
    (inScope : P → R → Prop) (c : P) (r : R)
    (hpriv : ∀ c, ¬ isPriv c) (hunowned : ∀ r, ¬ isUnowned r)
    (h : canAccess inScope isPriv isUnowned c r) : inScope c r := by
  rcases h with h | h | h
  · exact h
  · exact absurd h (hpriv c)
  · exact absurd h (hunowned r)

end PCA

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

