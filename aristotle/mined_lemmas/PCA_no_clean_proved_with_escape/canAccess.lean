import Mathlib

namespace PCA

section PCA

variable {P R : Type}

/-- A caller `c` can access a resource `r` if `r` is in `c`'s scope, or `c` is
privileged, or `r` is unowned. -/

def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Soundness-fuzz invariant: a clean-isolation proof (every access is in scope)
is incompatible with an escape firing out of scope. -/
