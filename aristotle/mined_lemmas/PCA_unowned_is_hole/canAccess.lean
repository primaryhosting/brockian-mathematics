import Mathlib

/-!
# Policy access model: unowned rows are a hole

A minimal model of a row-level access policy of the form

```
inScope(caller, row) OR isPrivileged(caller) OR row.owner IS NULL
```

The theorem `PCA.unowned_is_hole` records that the `IS NULL` (unowned) disjunct
lets *any* caller reach an unowned row.
-/

namespace PCA

section
variable {P R : Type}

/-- The access policy: a caller `c` can access a row `r` when the row is in the
caller's scope, or the caller is privileged, or the row is unowned. -/

def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Any caller can reach an unowned row (models the `IS NULL` hole). -/
