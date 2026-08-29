import Mathlib
import RequestProject.Main

/-!
# Mathlib-context restatement

The target theorem `PCA.leak_iff_escape_when_out_of_scope` lives in `RequestProject/Main.lean`,
which must begin with the prescribed module docstring and therefore cannot contain an `import`.
Here we re-derive the same statement inside a full Mathlib context, using the Mathlib lemma
`or_iff_right`, and check that it agrees with the target.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

variable {P R : Type}

/-- Same statement as the target, proved via the Mathlib lemma `or_iff_right`. -/
theorem leak_iff_escape_when_out_of_scope' (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) (h : ¬ inScope c r) :
    canAccess inScope isPriv isUnowned c r ↔ (isPriv c ∨ isUnowned r) :=
  or_iff_right h

example (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) (h : ¬ inScope c r) :
    canAccess inScope isPriv isUnowned c r ↔ (isPriv c ∨ isUnowned r) :=
  leak_iff_escape_when_out_of_scope inScope isPriv isUnowned c r h

end PCA

/-!
# Leak Iff Escape When Out Of Scope
Category: Proof-Carrying Apps (Lean)
Target: PCA.leak_iff_escape_when_out_of_scope
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header above is a module docstring, which Lean treats as a command,
-- so no `import` may follow it. The development below is therefore self-contained and
-- needs nothing beyond the Lean 4 prelude; see `RequestProject/MathlibCheck.lean` for the
-- same statement re-derived inside a Mathlib context (via `or_iff_right`).

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA

section

variable {P R : Type}

/-- A principal `c` may access a resource `r` when `r` is in `c`'s scope, or one of the
two "escape hatches" fires: `c` is privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Out of scope, access holds iff some escape fires: if `¬ inScope c r`, then
`canAccess inScope isPriv isUnowned c r` is equivalent to `isPriv c ∨ isUnowned r`. -/
theorem leak_iff_escape_when_out_of_scope
    (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) (h : ¬ inScope c r) :
    canAccess inScope isPriv isUnowned c r ↔ (isPriv c ∨ isUnowned r) :=
  Iff.intro
    (fun hacc => hacc.resolve_left h)
    (fun hesc => Or.inr hesc)

end

end PCA

