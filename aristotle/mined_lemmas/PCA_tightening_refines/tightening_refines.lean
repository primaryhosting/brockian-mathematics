/-!
# Tightening Refines
Category: Proof-Carrying Apps (Lean)
Target: PCA.tightening_refines
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header comment must be the very first thing in the file,
-- and Lean does not permit `import` after a module docstring, so this file is
-- self-contained and uses no imports. The proof needs no Mathlib machinery.

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

section
variable {P R : Type}

/-- Access is granted when the capability is in scope for the resource,
the capability is privileged, or the resource is unowned. -/

theorem tightening_refines (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) :
    canAccess inScope isPriv (fun _ => False) c r →
      canAccess inScope isPriv isUnowned c r := by
  rintro (h | h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact h.elim

end

end PCA

