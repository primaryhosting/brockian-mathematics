/-!
# Tightening Refines
Category: Proof-Carrying Apps (Lean)
Target: PCA.tightening_refines
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` commands to precede every other command, including the
-- module docstring above. Since the development below is self-contained and needs no
-- Mathlib lemmas, no imports are used, and the required header stays at the top of the file.

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

section PCA

variable {P R : Type}

/-- A principal `c` can access a resource `r` when `r` is in `c`'s scope, or `c` is
privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Tightening the policy by removing the "unowned" disjunct refines access: every
access permitted by the tightened policy is permitted by the original one. -/
theorem tightening_refines (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) :
    canAccess inScope isPriv (fun _ => False) c r → canAccess inScope isPriv isUnowned c r := by
  rintro (h | h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact absurd h not_false

end PCA

end PCA

#print axioms PCA.tightening_refines

