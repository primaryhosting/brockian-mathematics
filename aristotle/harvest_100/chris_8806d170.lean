import Mathlib

/-!
# Soundness-fuzz invariant for a policy/capability access model

A principal `c : P` can access a resource `r : R` when either `r` is in `c`'s scope,
or `c` is privileged, or `r` is unowned.  A *clean isolation proof* says every access
collapses to in-scope access; an *escape* is an out-of-scope pair witnessing privilege
or unownedness.  The two cannot coexist.
-/

namespace PCA

section
variable {P R : Type}

/-- `c` can access `r` if `r` is in scope for `c`, or `c` is privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- If a clean-isolation proof exists (every access is in-scope) yet an escape can fire
out of scope, we get a contradiction. -/
theorem no_clean_proved_with_escape
    {inScope : P → R → Prop} {isPriv : P → Prop} {isUnowned : R → Prop}
    (hclean : ∀ c r, canAccess inScope isPriv isUnowned c r → inScope c r)
    (hescape : ∃ c r, ¬ inScope c r ∧ (isPriv c ∨ isUnowned r)) : False := by
  obtain ⟨c, r, hns, hesc⟩ := hescape
  exact hns (hclean c r (Or.inr hesc))

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

