/-!
# Unowned Is Hole
Category: Proof-Carrying Apps (Lean)
Target: PCA.unowned_is_hole
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header above is a module docstring, and Lean requires that
-- every `import` command precede any other command in a file. The development
-- below therefore uses only core Lean 4 logic (`Or.inr`), which is available
-- unconditionally and is exactly what Mathlib's `exact?`/`apply?` find for this
-- goal (the disjunction introduction rule `Or.inr`).

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

variable {P R : Type}

/-- A caller `c` can access a row `r` when the row is in the caller's scope,
the caller is privileged, or the row is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Any caller can reach an unowned row: this models the `IS NULL` hole in the
access-control predicate. -/
theorem unowned_is_hole (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) (h : isUnowned r) :
    canAccess inScope isPriv isUnowned c r :=
  Or.inr (Or.inr h)

end PCA

#print axioms PCA.unowned_is_hole

