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
theorem unowned_is_hole (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) (h : isUnowned r) :
    canAccess inScope isPriv isUnowned c r :=
  Or.inr (Or.inr h)

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

