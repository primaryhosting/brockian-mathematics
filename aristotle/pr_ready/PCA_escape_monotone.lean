/-!
# Escape Monotone
Category: Proof-Carrying Apps (Lean)
Target: PCA.escape_monotone
Statement: Model (state inline): section PCA variable {P R : Type} def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop) (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r Theorem: Adding escapes only enlarges access: if inScope c r then canAccess inScope isPriv isUnowned c r.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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


namespace PCA

section PCA

variable {P R : Type}

/-- A principal `c` can access a resource `r` if `r` is in `c`'s scope, or `c` is
privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Adding escapes only enlarges access: being in scope implies access. -/
theorem escape_monotone (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) (h : inScope c r) :
    canAccess inScope isPriv isUnowned c r :=
  Or.inl h

end PCA

end PCA

