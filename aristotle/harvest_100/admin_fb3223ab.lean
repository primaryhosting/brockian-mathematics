/-!
# No Escape No Leak
Category: Proof-Carrying Apps (Lean)
Target: PCA.no_escape_no_leak
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other command,
-- including module doc comments, so the mandated header above must be the whole
-- prelude of this file. The development below is pure logic and needs no
-- Mathlib lemmas; it elaborates against the Lean 4 core prelude inside this
-- Mathlib project.

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

section PCA

variable {P R : Type}

/-- Access is granted when the capability is in scope for the resource, or the
capability is privileged, or the resource is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- **No escape, no leak.** If there are no privileged capabilities and no unowned
resources, then every granted access is in-scope. -/
theorem no_escape_no_leak (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R)
    (hpriv : ∀ c, ¬ isPriv c) (hunowned : ∀ r, ¬ isUnowned r)
    (h : canAccess inScope isPriv isUnowned c r) : inScope c r := by
  rcases h with h | h | h
  · exact h
  · exact absurd h (hpriv c)
  · exact absurd h (hunowned r)

end PCA

end PCA

#print axioms PCA.no_escape_no_leak

