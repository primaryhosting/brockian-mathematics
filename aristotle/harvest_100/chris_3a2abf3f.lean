/-!
# Unowned Is Hole
Category: Proof-Carrying Apps (Lean)
Target: PCA.unowned_is_hole
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header above is a module docstring, which Lean requires to be the
-- first command in the file; consequently no `import` line may precede it. The development
-- below needs nothing beyond Lean 4 core (the closing lemma is `Or.inr`, i.e.
-- `Or.intro_right`, which is core and is also what `exact?` finds in a Mathlib session),
-- so the file is self-contained and compiles inside this Mathlib-based project.

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

section
variable {P R : Type}

/-- Access policy: a caller `c` may access a row `r` when the row is in the caller's
scope, or the caller is privileged, or the row is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Any caller can reach an unowned row (models the `IS NULL` hole).

The proof is two right-introductions of disjunction: `Or.inr` (`Or.intro_right`). -/
theorem unowned_is_hole (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) (h : isUnowned r) :
    canAccess inScope isPriv isUnowned c r :=
  Or.inr (Or.inr h)

end

end PCA

#print axioms PCA.unowned_is_hole

