import Mathlib
import RequestProject.Main

/-!
Companion file: the same statement re-checked in a Mathlib context, proved via the
Mathlib/core lemma `Or.resolve_right` (together with `not_or`).
-/

set_option autoImplicit false

namespace PCA

section
variable {P R : Type}

/-- Mathlib-context restatement of `PCA.no_escape_no_leak`, proved with
`Or.resolve_right` and `not_or`. -/
theorem no_escape_no_leak' (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R)
    (hpriv : ∀ c, ¬ isPriv c) (hunowned : ∀ r, ¬ isUnowned r)
    (h : canAccess inScope isPriv isUnowned c r) : inScope c r :=
  h.resolve_right (not_or.mpr ⟨hpriv c, hunowned r⟩)

end

end PCA

#print axioms PCA.no_escape_no_leak
#print axioms PCA.no_escape_no_leak'

/-!
# No Escape No Leak
Category: Proof-Carrying Apps (Lean)
Target: PCA.no_escape_no_leak
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header comment above is a module docstring, which Lean treats
-- as a command; hence no `import` may follow it. The development below is
-- self-contained and needs nothing beyond Lean core (see `RequestProject/MathlibCheck.lean`
-- for the same statement checked in a Mathlib context).

set_option autoImplicit false

namespace PCA

section
variable {P R : Type}

/-- Access is granted when the capability is in scope, or the capability is
privileged, or the resource is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- With no privileged capabilities and no unowned resources, any granted access
is in-scope. -/
theorem no_escape_no_leak (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R)
    (hpriv : ∀ c, ¬ isPriv c) (hunowned : ∀ r, ¬ isUnowned r)
    (h : canAccess inScope isPriv isUnowned c r) : inScope c r := by
  cases h with
  | inl h => exact h
  | inr h =>
    cases h with
    | inl h => exact absurd h (hpriv c)
    | inr h => exact absurd h (hunowned r)

end

end PCA

#print axioms PCA.no_escape_no_leak

