import Mathlib

/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps (Lean)
Target: PCA.with_check_true_admits_forge
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

section

variable {P R : Type}

/-- Access predicate of the row-level security model: a principal `c` may access a row `r`
when the row is in scope for `c`, the principal is privileged, or the row is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- A `WITH CHECK true` write policy admits every row for every principal, i.e. it
models a "forge-any" capability: no write is ever rejected. -/
theorem with_check_true_admits_forge :
    let canWrite : P → R → Prop := fun (_ : P) (_ : R) => True
    ∀ (c : P) (r : R), canWrite c r := by
  intro canWrite c r
  trivial

end

end PCA

