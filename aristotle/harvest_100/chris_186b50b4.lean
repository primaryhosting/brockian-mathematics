import Mathlib

/-!
# Rice Nontrivial
Category: Computer Science
Target: CS.rice_nontrivial
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

open Nat.Partrec Nat.Partrec.Code ComputablePred

/-- **Rice's theorem, nontrivial form.**

A property `P` of programs (here: of partial recursive codes) is *semantic* (extensional) if it
depends only on the partial function `eval c` computed by the code `c`.  It is *nontrivial* if some
program satisfies it and some program does not.

Every nontrivial semantic property of programs is undecidable. -/
theorem rice_nontrivial (P : Code → Prop)
    (hsem : ∀ c₁ c₂ : Code, eval c₁ = eval c₂ → (P c₁ ↔ P c₂))
    (cyes cno : Code) (hyes : P cyes) (hno : ¬ P cno) :
    ¬ ComputablePred P := by
  intro hcomp
  have h := (ComputablePred.rice₂ {c : Code | P c} hsem).1 hcomp
  rcases h with h | h
  · exact absurd (show cyes ∈ {c : Code | P c} from hyes) (by simp [h])
  · exact hno (show cno ∈ {c : Code | P c} by simp [h])

/-- A corollary: the set of programs computing a fixed nontrivially-realized partial function is
undecidable.  Concretely, deciding whether a program halts on input `n` is impossible. -/
theorem halting_undecidable (n : ℕ) : ¬ ComputablePred fun c : Code => (eval c n).Dom :=
  ComputablePred.halting_problem n

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

