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
