/-!
# Leak Iff Escape When Out Of Scope
Category: Proof-Carrying Apps (Lean)
Target: PCA.leak_iff_escape_when_out_of_scope
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` lines to precede every other command, including
-- module doc comments, so the mandated header above is kept at the very top and
-- this file uses no imports; the development is pure logic and needs none.

set_option autoImplicit false

namespace PCA

section
variable {P R : Type}

/-- Access is granted when the capability is in scope for the resource, or one of the
two escape hatches fires: the capability is privileged, or the resource is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Out of scope, access holds iff some escape fires. -/
theorem leak_iff_escape_when_out_of_scope
    (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) (h : ¬ inScope c r) :
    canAccess inScope isPriv isUnowned c r ↔ (isPriv c ∨ isUnowned r) := by
  constructor
  · rintro (hs | hesc)
    · exact absurd hs h
    · exact hesc
  · intro hesc
    exact Or.inr hesc

end

end PCA

#print axioms PCA.leak_iff_escape_when_out_of_scope

