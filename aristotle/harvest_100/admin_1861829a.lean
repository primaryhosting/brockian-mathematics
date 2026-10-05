/-!
# Default Deny
Category: Proof-Carrying Apps (Lean)
Target: PCA.default_deny
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` lines to precede every other command, including
-- module doc comments, so the mandated header above forces this module to be
-- import-free.  The development below is pure logic and needs no Mathlib
-- machinery; `RequestProject.Main` imports Mathlib together with this module and
-- re-derives the result there using Mathlib's `not_or` (see `PCA.default_deny'`).

namespace PCA

section

variable {P R : Type}

/-- A capability `c` may access a resource `r` when `r` lies in the scope of `c`,
or `c` is privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- **Default deny**: with an empty scope relation and no escape hatches
(no privileged capabilities, no unowned resources), nothing is accessible. -/
theorem default_deny {inScope : P → R → Prop} {isPriv : P → Prop} {isUnowned : R → Prop}
    (hscope : ∀ (c : P) (r : R), ¬ inScope c r) (hpriv : ∀ c : P, ¬ isPriv c)
    (hown : ∀ r : R, ¬ isUnowned r) (c : P) (r : R) :
    ¬ canAccess inScope isPriv isUnowned c r := by
  rintro (h | h | h)
  · exact hscope c r h
  · exact hpriv c h
  · exact hown r h

end

end PCA

import Mathlib
import RequestProject.PCA

/-!
# Default Deny
Category: Proof-Carrying Apps (Lean)
Target: PCA.default_deny
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace PCA

variable {P R : Type}

/-- Mathlib-flavoured restatement of `PCA.default_deny`, closed via Mathlib's
`not_or` (`¬(a ∨ b) ↔ ¬a ∧ ¬b`). -/
theorem default_deny' {inScope : P → R → Prop} {isPriv : P → Prop} {isUnowned : R → Prop}
    (hscope : ∀ (c : P) (r : R), ¬ inScope c r) (hpriv : ∀ c : P, ¬ isPriv c)
    (hown : ∀ r : R, ¬ isUnowned r) (c : P) (r : R) :
    ¬ canAccess inScope isPriv isUnowned c r := by
  rw [canAccess, not_or, not_or]
  exact ⟨hscope c r, hpriv c, hown r⟩

end PCA

#print axioms PCA.default_deny
#print axioms PCA.default_deny'

