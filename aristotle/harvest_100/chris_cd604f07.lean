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

section PCA

variable {P R : Type}

/-- A principal `c` can access a resource `r` when `r` is in `c`'s scope, or `c` is
privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- A `WITH CHECK true` write policy admits any row: it models a forge-any capability,
since every principal may write every resource. -/
theorem with_check_true_admits_forge :
    let canWrite := fun (_ : P) (_ : R) => True
    ∀ (c : P) (r : R), canWrite c r := by
  intro canWrite c r
  trivial

end PCA

end PCA

