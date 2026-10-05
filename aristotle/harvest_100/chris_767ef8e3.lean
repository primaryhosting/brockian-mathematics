/-
# No Clean Proved With Escape
Category: Proof-Carrying Apps (Lean)
Target: PCA.no_clean_proved_with_escape
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# No Clean Proved With Escape
Category: Proof-Carrying Apps (Lean)
Target: PCA.no_clean_proved_with_escape
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

/-- A principal `c` can access a resource `r` when `r` is in `c`'s scope, or `c` is
privileged, or `r` is unowned. -/
def canAccess (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (c : P) (r : R) : Prop := inScope c r ∨ isPriv c ∨ isUnowned r

/-- Soundness-fuzz invariant: a clean-isolation proof (every access is in scope)
is incompatible with an escape firing out of scope. -/
theorem no_clean_proved_with_escape
    (inScope : P → R → Prop) (isPriv : P → Prop) (isUnowned : R → Prop)
    (hclean : ∀ (c : P) (r : R), canAccess inScope isPriv isUnowned c r → inScope c r)
    (hescape : ∃ (c : P) (r : R), ¬ inScope c r ∧ (isPriv c ∨ isUnowned r)) :
    False := by
  obtain ⟨c, r, hns, hesc⟩ := hescape
  refine hns (hclean c r ?_)
  rcases hesc with hp | hu
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr hu)

end

end PCA

