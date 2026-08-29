import Mathlib

/-!
# Tightening Refines
Category: Proof-Carrying Apps (Lean)
Target: PCA.tightening_refines
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

set_option grind.warning false

namespace PCA

section
variable {P R : Type}

/-- Access predicate: a principal `c` may access resource `r` when `r` is in `c`'s scope,
or `c` is privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Removing the "unowned" disjunct tightens the policy: any access granted by the
tightened policy is also granted by the original one. -/
theorem tightening_refines (inScope : P → R → Prop) (isPriv : P → Prop)
    (isUnowned : R → Prop) (c : P) (r : R) :
    canAccess inScope isPriv (fun _ => False) c r → canAccess inScope isPriv isUnowned c r := by
  intro h
  rcases h with hs | hp | hf
  · exact Or.inl hs
  · exact Or.inr (Or.inl hp)
  · exact absurd hf not_false

end

end PCA

