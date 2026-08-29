import Mathlib

/-!
# Owner Only Isolated
Category: Proof-Carrying Apps (Lean)
Target: PCA.owner_only_isolated
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- A principal `c` can access a resource `r` when `r` is in `c`'s scope, or `c` is
privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Owner-equality scope with no escapes (no privileged principals, no unowned
resources) is isolated: access implies ownership. -/
theorem owner_only_isolated (ownerOf : R → P) (c : P) (r : R)
    (h : canAccess (fun c r => ownerOf r = c) (fun _ => False) (fun _ => False) c r) :
    ownerOf r = c := by
  rcases h with h | h | h
  · exact h
  · exact h.elim
  · exact h.elim

end PCA

end PCA

