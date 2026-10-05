import Mathlib
import RequestProject.Main

/-!
# `PCA.unowned_is_hole` in the presence of Mathlib

This module re-checks the target theorem with all of `Mathlib` in scope, and records
that its proof uses no axioms at all.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

example {P R : Type} {inScope : P → R → Prop} {isPriv : P → Prop}
    {isUnowned : R → Prop} {c : P} {r : R} (h : isUnowned r) :
    canAccess inScope isPriv isUnowned c r :=
  unowned_is_hole h

/-- Conversely, unowned-ness is the only extra reachability the disjunct adds:
`canAccess` is exactly the three-way disjunction. -/
example {P R : Type} {inScope : P → R → Prop} {isPriv : P → Prop}
    {isUnowned : R → Prop} {c : P} {r : R} :
    canAccess inScope isPriv isUnowned c r ↔ inScope c r ∨ isPriv c ∨ isUnowned r :=
  Iff.rfl

end PCA

#print axioms PCA.unowned_is_hole

/-!
# Unowned Is Hole
Category: Proof-Carrying Apps (Lean)
Target: PCA.unowned_is_hole
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- NOTE: Lean requires every `import` to precede all other commands, including the
-- module docstring above. Since the requested header must be the very first thing in
-- the file, this module carries no imports; the development needs none. The companion
-- module `RequestProject.PCAMathlib` imports both `Mathlib` and this file and re-checks
-- the target there.

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

variable {P R : Type}

/-- A caller `c` can access a row `r` when the row is in the caller's scope, or the
caller is privileged, or the row is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- **Unowned is a hole**: any caller can reach an unowned row, which models the
`IS NULL` hole in an ownership check.

The proof is right-introduction of a disjunction, twice: `Or.intro_right`
(notation `Or.inr`) from Lean core / Mathlib's `Logic` layer. -/
theorem unowned_is_hole {inScope : P → R → Prop} {isPriv : P → Prop}
    {isUnowned : R → Prop} {c : P} {r : R} (h : isUnowned r) :
    canAccess inScope isPriv isUnowned c r :=
  Or.intro_right _ (Or.intro_right _ h)

end PCA

