import Mathlib

/-!
# No Escape No Leak
Category: Proof-Carrying Apps (Lean)
Target: PCA.no_escape_no_leak
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command, including
-- module docstrings, so the required header comment is placed immediately after
-- the single `import Mathlib` line.

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

section PCA

variable {P R : Type}

/-- Access is granted when the capability is in scope for the resource, or the
capability is privileged, or the resource is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- **No escape, no leak**: if there are no privileged capabilities and no unowned
resources, then every granted access is in-scope.

The core step is the Mathlib/core lemma `Or.resolve_right : a ∨ b → ¬b → a`,
applied to the disjunction that `canAccess` unfolds to. -/
theorem no_escape_no_leak {isPriv : P → Prop} {isUnowned : R → Prop}
    (inScope : P → R → Prop) (c : P) (r : R)
    (hpriv : ∀ c, ¬ isPriv c) (hunowned : ∀ r, ¬ isUnowned r)
    (h : canAccess inScope isPriv isUnowned c r) : inScope c r :=
  h.resolve_right (fun hor => hor.elim (hpriv c) (hunowned r))

end PCA

end PCA

