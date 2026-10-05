/-!
# Default Deny
Category: Proof-Carrying Apps (Lean)
Target: PCA.default_deny
Statement: Model (state inline): section PCA variable {P R : Type} def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop) (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r Theorem: With empty scope and no escapes, nothing is accessible: (∀ c r, ¬inScope c r) → (∀ c, ¬isPriv c) → (∀ r, ¬isUnowned r) → ¬ canAccess inScope isPriv isUnowned c r.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace PCA

section
variable {P R : Type}

/-- A principal `c` can access a resource `r` when `r` is in `c`'s scope, or `c` is
privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Default deny: with an empty scope relation and no escape hatches
(no privileged principals, no unowned resources), nothing is accessible. -/
theorem default_deny {inScope : P → R → Prop} {isPriv : P → Prop} {isUnowned : R → Prop}
    {c : P} {r : R}
    (hscope : ∀ c r, ¬ inScope c r) (hpriv : ∀ c, ¬ isPriv c) (hown : ∀ r, ¬ isUnowned r) :
    ¬ canAccess inScope isPriv isUnowned c r := by
  rintro (h | h | h)
  · exact hscope c r h
  · exact hpriv c h
  · exact hown r h

end

end PCA


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

