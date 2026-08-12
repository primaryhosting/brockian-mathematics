import Mathlib

/-!
# Policy-check access model

A minimal model of row-level access policies, and the observation that a
`WITH CHECK true` write policy admits every row (i.e. it permits forging
arbitrary rows).
-/

namespace PCA

section PCA

variable {P R : Type}

/-- A principal `c` can access row `r` when the row is in the principal's
scope, the principal is privileged, or the row is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- A `WITH CHECK true` write policy admits any row: models forge-any. -/
theorem with_check_true_admits_forge :
    let canWrite : P → R → Prop := fun _ _ => True
    ∀ c : P, ∀ r : R, canWrite c r := by
  intro canWrite c r
  trivial

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

