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

