/-!
# Unowned Is Hole
Category: Proof-Carrying Apps (Lean)
Target: PCA.unowned_is_hole
Statement: Model (state inline): section PCA variable {P R : Type} def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop) (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r Theorem: Any caller can reach an unowned row (models the `IS NULL` hole): isUnowned r → canAccess inScope isPriv isUnowned c r.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace PCA

section PCA

variable {P R : Type}

/-- A caller `c` may access row `r` if the row is in scope for the caller,
the caller is privileged, or the row is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Any caller can reach an unowned row: this models the `IS NULL` hole in the policy. -/
theorem unowned_is_hole (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) (h : isUnowned r) : canAccess inScope isPriv isUnowned c r :=
  Or.inr (Or.inr h)

end PCA

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

