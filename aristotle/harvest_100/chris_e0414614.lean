/-!
# Escape Monotone
Category: Proof-Carrying Apps (Lean)
Target: PCA.escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

section
variable {P R : Type}

/-- Access is granted when the capability is in scope, or the capability is
privileged, or the resource is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Adding escape hatches (privilege, unowned resources) only enlarges access:
being in scope already suffices for access.  This is closed by the Mathlib/core
lemma `Or.inl` (found by `exact?`). -/
theorem escape_monotone (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) (h : inScope c r) :
    canAccess inScope isPriv isUnowned c r :=
  Or.inl h

/-- `canAccess` is monotone in each of its three policy predicates: weakening the
scope relation, or the privilege / unowned predicates, only enlarges access. -/
theorem canAccess_mono {inScope inScope' : P → R → Prop} {isPriv isPriv' : P → Prop}
    {isUnowned isUnowned' : R → Prop}
    (hs : ∀ c r, inScope c r → inScope' c r) (hp : ∀ c, isPriv c → isPriv' c)
    (hu : ∀ r, isUnowned r → isUnowned' r) (c : P) (r : R)
    (h : canAccess inScope isPriv isUnowned c r) :
    canAccess inScope' isPriv' isUnowned' c r :=
  h.imp (hs c r) (Or.imp (hp c) (hu r))

end

end PCA

#print axioms PCA.escape_monotone
#print axioms PCA.canAccess_mono

