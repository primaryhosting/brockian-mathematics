/-!
# Unowned Is Hole
Category: Proof-Carrying Apps (Lean)
Target: PCA.unowned_is_hole
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA

section PCA

variable {P R : Type}

/-- Access policy: a caller `c` may access a row `r` when the row is in the caller's
scope, or the caller is privileged, or the row is unowned. -/

theorem unowned_is_hole (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) (h : isUnowned r) :
    canAccess inScope isPriv isUnowned c r :=
  Or.inr (Or.inr h)

end PCA

end PCA

#print axioms PCA.unowned_is_hole

