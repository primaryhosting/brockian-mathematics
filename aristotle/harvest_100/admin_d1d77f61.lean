/-!
# Priv Is Escape
Category: Proof-Carrying Apps (Lean)
Target: PCA.priv_is_escape
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header above is a module docstring, which Lean requires to
-- precede any `import` command; the development below is self-contained and needs
-- no imports beyond Lean core (the project still depends on Mathlib).

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

section
variable {P R : Type}

/-- Access is granted when the resource is in the caller's scope, the caller is
privileged, or the resource is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- A privileged caller always has access (models the admin bypass). -/
theorem priv_is_escape (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) (h : isPriv c) :
    canAccess inScope isPriv isUnowned c r :=
  Or.inr (Or.inl h)

end

end PCA

#print axioms PCA.priv_is_escape

