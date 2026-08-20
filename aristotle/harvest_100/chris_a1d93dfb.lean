/-!
# Owner Only Isolated
Category: Proof-Carrying Apps (Lean)
Target: PCA.owner_only_isolated
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

section PCA

variable {P R : Type}

/-- A principal `c` can access a resource `r` when `r` is in `c`'s scope,
or `c` is privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Owner-equality scope with no privileged principals and no unowned resources
is isolated: any access implies ownership. -/
theorem owner_only_isolated (ownerOf : R → P) (c : P) (r : R)
    (h : canAccess (fun c r => ownerOf r = c) (fun _ => False) (fun _ => False) c r) :
    ownerOf r = c := by
  rcases h with h | h | h
  · exact h
  · exact h.elim
  · exact h.elim

end PCA

end PCA

#print axioms PCA.owner_only_isolated

