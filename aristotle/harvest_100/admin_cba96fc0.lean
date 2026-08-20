/-
# With Check True Admits Forge
Category: Proof-Carrying Apps (Lean)
Target: PCA.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

namespace PCA

section
variable {P R : Type}

/-- Access policy: a principal `c` may access resource `r` if it is in scope,
the principal is privileged, or the resource is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- A `WITH CHECK true` write policy admits any row: it models a forge-any capability. -/
theorem with_check_true_admits_forge :
    ∀ (canWrite : P → R → Prop), (canWrite = fun (_ : P) (_ : R) => True) →
      ∀ (c : P) (r : R), canWrite c r := by
  rintro canWrite rfl c r
  trivial

end

end PCA

