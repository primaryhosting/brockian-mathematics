import Mathlib

/-!
# Policy-Controlled Access (PCA): owner-only scope is isolated

A minimal access-control model: a principal `c` can access a resource `r`
when `r` is in `c`'s scope, or `c` is privileged, or `r` is unowned.
-/

namespace PCA

section
variable {P R : Type}

/-- `c` can access `r` iff `r` is in scope for `c`, or `c` is privileged,
or `r` is unowned. -/

def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- With owner-equality scope, no privileged principals and no unowned resources,
access implies ownership. -/
