/-!
# Default Deny
Category: Proof-Carrying Apps (Lean)
Target: PCA.default_deny
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header comment above is a module docstring, which Lean requires
-- to precede every command, including `import`s.  The development below is pure
-- propositional logic and needs no imports beyond the prelude; `not_or`, cited in the
-- proof, is available in the Lean core / Mathlib environment.

set_option autoImplicit false

namespace PCA

section PCA

variable {P R : Type}

/-- A client `c` can access a resource `r` when `r` is in `c`'s scope, or `c` is
privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- **Default deny**: with an empty scope relation and no escape hatches
(no privileged clients, no unowned resources), nothing is accessible.

The proof is a direct application of the library lemma `not_or`
(`¬(p ∨ q) ↔ ¬p ∧ ¬q`), used twice to split the three disjuncts. -/
theorem default_deny {inScope : P → R → Prop} {isPriv : P → Prop} {isUnowned : R → Prop}
    {c : P} {r : R} (hscope : ∀ c r, ¬ inScope c r) (hpriv : ∀ c, ¬ isPriv c)
    (hown : ∀ r, ¬ isUnowned r) : ¬ canAccess inScope isPriv isUnowned c r :=
  not_or.mpr ⟨hscope c r, not_or.mpr ⟨hpriv c, hown r⟩⟩

end PCA

end PCA

#print axioms PCA.default_deny

