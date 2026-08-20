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

def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Removing the "unowned" disjunct tightens the policy: any access permitted by
the tightened policy is also permitted by the original policy. -/
