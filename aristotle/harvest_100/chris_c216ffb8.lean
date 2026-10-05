/-!
# Unowned Is Hole
Category: Proof-Carrying Apps (Lean)
Target: PCA.unowned_is_hole
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

namespace PCA

section PCA

variable {P R : Type}

/-- A caller `c` can access a row `r` when the row is in the caller's scope,
the caller is privileged, or the row is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Contrapositive form of the hole: if a caller cannot access a row, then the row
is owned (and moreover it is out of scope and the caller is unprivileged). -/
theorem not_canAccess_imp_not_isUnowned (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R)
    (h : ¬ canAccess inScope isPriv isUnowned c r) : ¬ isUnowned r :=
  fun hu => h (Or.inr (Or.inr hu))

/-- Any caller can reach an unowned row: this models the `IS NULL` hole. -/
theorem unowned_is_hole (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) (h : isUnowned r) :
    canAccess inScope isPriv isUnowned c r :=
  Or.inr (Or.inr h)

end PCA

end PCA

#print axioms PCA.unowned_is_hole

