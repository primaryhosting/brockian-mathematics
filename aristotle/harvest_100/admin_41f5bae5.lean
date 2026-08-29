import Mathlib
import RequestProject.Main

/-!
# Escape Monotone — Mathlib-side check

This module imports Mathlib together with the self-contained development in
`RequestProject.Main`, and records that the target theorem is axiom-clean.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA

-- `propext`, `Classical.choice`, `Quot.sound` are the only axioms permitted; in fact the proof
-- below uses none of them.
#print axioms PCA.escape_monotone

example {P R : Type} (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) (h : inScope c r) : canAccess inScope isPriv isUnowned c r := by
  exact escape_monotone inScope isPriv isUnowned c r h

end PCA

/-!
# Escape Monotone
Category: Proof-Carrying Apps (Lean)
Target: PCA.escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header comment must be the first thing in the file, and Lean 4 requires
-- `import` commands to precede every other command (including module documentation).  The
-- development below is entirely self-contained and needs nothing from Mathlib, so no imports
-- are used here.  See `RequestProject/EscapeMathlib.lean` for the same results re-checked in a
-- Mathlib-importing module.

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA

section
variable {P R : Type}

/-- A principal `c` can access a resource `r` when `r` is in `c`'s scope, or one of the
"escape hatches" applies: `c` is privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Adding escapes only enlarges access: if `c` is in scope for `r`, then `c` can access `r`. -/
theorem escape_monotone (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) (h : inScope c r) :
    canAccess inScope isPriv isUnowned c r :=
  Or.inl h

end

end PCA

