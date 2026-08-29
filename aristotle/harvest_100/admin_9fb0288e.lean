/-
# Unowned Is Hole
Category: Proof-Carrying Apps (Lean)
Target: PCA.unowned_is_hole
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Unowned Is Hole
Category: Proof-Carrying Apps (Lean)
Target: PCA.unowned_is_hole
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA

section
variable {P R : Type}

/-- Access policy: a caller `c` may access a row `r` when the row is in the
caller's scope, or the caller is privileged, or the row is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Contrapositive form of the policy: access is denied exactly when the row is
out of scope, the caller is unprivileged, and the row is owned. -/
theorem not_canAccess_iff (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) :
    ¬ canAccess inScope isPriv isUnowned c r ↔
      (¬ inScope c r ∧ ¬ isPriv c ∧ ¬ isUnowned r) := by
  unfold canAccess
  tauto

/-- Any caller can reach an unowned row (models the `IS NULL` hole). -/
theorem unowned_is_hole (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) (h : isUnowned r) :
    canAccess inScope isPriv isUnowned c r :=
  Or.inr (Or.inr h)

end

end PCA

