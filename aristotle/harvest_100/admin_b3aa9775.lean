/-
# Rice Nontrivial
Category: Computer Science
Target: CS.rice_nontrivial
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Rice Nontrivial
Category: Computer Science
Target: CS.rice_nontrivial
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- **Rice's theorem**: every nontrivial semantic (extensional) property of programs is
undecidable.

Here programs are the codes of partial recursive functions (`Nat.Partrec.Code`), `P` is
*semantic* if it only depends on the denotation `eval c` of the code, and *nontrivial* if some
program satisfies it and some program does not.  Then `P` is not a decidable (computable)
predicate.

This is derived from Mathlib's `ComputablePred.rice₂`. -/
theorem rice_nontrivial (P : Code → Prop)
    (hsem : ∀ c d : Code, eval c = eval d → (P c ↔ P d))
    (c₁ c₂ : Code) (h₁ : P c₁) (h₂ : ¬ P c₂) :
    ¬ ComputablePred P := by
  intro h
  have key := (ComputablePred.rice₂ {c | P c} hsem).1 h
  rcases key with he | hu
  · exact absurd (Set.eq_empty_iff_forall_notMem.1 he c₁) (by simpa using h₁)
  · exact h₂ (by simpa using (Set.eq_univ_iff_forall.1 hu c₂))

end CS

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

