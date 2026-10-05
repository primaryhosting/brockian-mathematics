/-!
# Leak Iff Escape When Out Of Scope
Category: Proof-Carrying Apps (Lean)
Target: PCA.leak_iff_escape_when_out_of_scope
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA

section PCA

variable {P R : Type}

/-- Access is granted when the capability is in scope for the resource,
or one of the escape hatches fires (privileged capability, unowned resource). -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Out of scope, access holds iff some escape fires. -/
theorem leak_iff_escape_when_out_of_scope
    (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) (h : ¬ inScope c r) :
    canAccess inScope isPriv isUnowned c r ↔ (isPriv c ∨ isUnowned r) := by
  unfold canAccess
  constructor
  · rintro (hs | he)
    · exact absurd hs h
    · exact he
  · intro he
    exact Or.inr he

end PCA

end PCA

