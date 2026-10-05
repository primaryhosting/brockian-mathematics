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

theorem not_canAccess_iff (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) :
    ¬ canAccess inScope isPriv isUnowned c r ↔
      (¬ inScope c r ∧ ¬ isPriv c ∧ ¬ isUnowned r) := by
  unfold canAccess
  tauto

/-- Any caller can reach an unowned row (models the `IS NULL` hole). -/
