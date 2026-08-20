import Mathlib
import RequestProject.Main

/-!
# Mathlib-context check

Re-derivation of `PCA.leak_iff_escape_when_out_of_scope` inside a full Mathlib
environment, together with an axiom check.
-/

namespace PCA

example {P R : Type} (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) (h : ¬ inScope c r) :
    canAccess inScope isPriv isUnowned c r ↔ (isPriv c ∨ isUnowned r) := by
  unfold canAccess
  tauto

#print axioms PCA.leak_iff_escape_when_out_of_scope

end PCA

/-!
# Leak Iff Escape When Out Of Scope
Category: Proof-Carrying Apps (Lean)
Target: PCA.leak_iff_escape_when_out_of_scope
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header comment must be the first thing in the file, and Lean
-- forbids `import` after any command, so this module is kept import-free; the proof
-- below uses only core logic. See `RequestProject/MathlibCheck.lean` for the same
-- statement re-checked in a Mathlib context.

namespace PCA

section

variable {P R : Type}

/-- Access is granted when the capability is in scope for the resource, or an
"escape hatch" fires: the capability is privileged, or the resource is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Out of scope, access holds iff some escape fires. -/
theorem leak_iff_escape_when_out_of_scope
    (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) (h : ¬ inScope c r) :
    canAccess inScope isPriv isUnowned c r ↔ (isPriv c ∨ isUnowned r) := by
  constructor
  · intro hacc
    rcases hacc with hs | hesc
    · exact absurd hs h
    · exact hesc
  · intro hesc
    exact Or.inr hesc

end

end PCA

