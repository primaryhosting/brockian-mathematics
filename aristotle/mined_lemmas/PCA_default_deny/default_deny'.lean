/-!
# Default Deny
Category: Proof-Carrying Apps (Lean)
Target: PCA.default_deny
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` lines to precede every other command, including
-- module doc comments, so the mandated header above forces this module to be
-- import-free.  The development below is pure logic and needs no Mathlib
-- machinery; `RequestProject.Main` imports Mathlib together with this module and
-- re-derives the result there using Mathlib's `not_or` (see `PCA.default_deny'`).

namespace PCA

section

variable {P R : Type}

/-- A capability `c` may access a resource `r` when `r` lies in the scope of `c`,
or `c` is privileged, or `r` is unowned. -/

theorem default_deny' {inScope : P → R → Prop} {isPriv : P → Prop} {isUnowned : R → Prop}
    (hscope : ∀ (c : P) (r : R), ¬ inScope c r) (hpriv : ∀ c : P, ¬ isPriv c)
    (hown : ∀ r : R, ¬ isUnowned r) (c : P) (r : R) :
    ¬ canAccess inScope isPriv isUnowned c r := by
  rw [canAccess, not_or, not_or]
  exact ⟨hscope c r, hpriv c, hown r⟩

end PCA

#print axioms PCA.default_deny
#print axioms PCA.default_deny'

