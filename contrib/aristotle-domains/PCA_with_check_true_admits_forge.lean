/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps (Lean)
Target: PCA.with_check_true_admits_forge
Statement: Model (state inline): section PCA variable {P R : Type} def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop) (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r Theorem: A `WITH CHECK true` write policy admits any row (models forge-any): let canWrite := fun (_ : P) (_ : R) => True; ∀ c r, canWrite c r.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace PCA

section PCA

variable {P R : Type}

/-- A caller `c` can access a row `r` if the row is in the caller's scope, or the
caller is privileged, or the row is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- A `WITH CHECK true` write policy admits any row: the resulting write
predicate holds for every caller and every row, so any row can be forged. -/
theorem with_check_true_admits_forge :
    let canWrite : P → R → Prop := fun _ _ => True
    ∀ c r, canWrite c r := by
  intro canWrite c r
  trivial

end PCA

end PCA


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

