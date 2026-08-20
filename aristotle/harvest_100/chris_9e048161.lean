import Mathlib

/-!
# Default Deny
Category: Proof-Carrying Apps (Lean)
Target: PCA.default_deny
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command, including
-- module doc comments, so the required header appears immediately after the import.

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

section
variable {P R : Type}

/-- A principal `c` can access a resource `r` when `r` is in `c`'s scope,
or `c` is privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- **Default deny**: with an empty scope and no escape hatches
(no privileged principals, no unowned resources), nothing is accessible.

The proof is the elimination of the two disjunctions; equivalently it is
`not_or.mpr ⟨hScope c r, not_or.mpr ⟨hPriv c, hUnowned r⟩⟩`, using Mathlib's
`not_or : ¬(a ∨ b) ↔ ¬a ∧ ¬b`. -/
theorem default_deny {inScope : P → R → Prop} {isPriv : P → Prop} {isUnowned : R → Prop}
    (hScope : ∀ c r, ¬ inScope c r) (hPriv : ∀ c, ¬ isPriv c) (hUnowned : ∀ r, ¬ isUnowned r)
    (c : P) (r : R) : ¬ canAccess inScope isPriv isUnowned c r :=
  not_or.mpr ⟨hScope c r, not_or.mpr ⟨hPriv c, hUnowned r⟩⟩

end

end PCA

#print axioms PCA.default_deny

