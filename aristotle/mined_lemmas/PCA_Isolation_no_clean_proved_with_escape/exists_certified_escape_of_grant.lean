import PCA.Isolation

/-!
# No Clean Proved With Escape
Category: Proof-Carrying Apps
Target: PCA.Isolation.no_clean_proved_with_escape
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Isolation

/-- Resources that a proof-carrying app may touch (files, sockets, ...). -/
abbrev Resource := Nat

/-- A capability set: the resources an app is entitled to touch. -/
abbrev Caps := Resource → Prop

/-- Inclusion of capability sets. -/

theorem exists_certified_escape_of_grant :
    ∃ (p : Prog) (P T : Caps) (t : List Resource),
      ¬ Clean p ∧ Certified P p T ∧ Run p t ∧ Escapes P t := by
  refine ⟨.seq (.grant 1) (.access 1), fun r => r = 0, Caps.add 1 (fun r => r = 0),
    [1], by simp [Clean], Certified.seq Certified.grant (Certified.access ?_), ?_,
    ⟨1, by simp⟩⟩
  · exact Or.inl rfl
  · have h := Run.seq (Run.grant 1) (Run.access 1)
    simpa using h

end PCA.Isolation

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

