import Mathlib
/-!
# Self Nonprediction
Category: Frontier Mind
Target: Frontier.self_nonprediction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

/-!
## The abstract diagonal argument

A "self-prediction system" is a collection `M` of machines, where `out m` is the next
output of machine `m` and `pred m` is the prediction that machine `m` makes about that
output *before* producing it.  If the collection is closed under diagonalization -- i.e.
it contains a machine that first consults its own prediction and then outputs the
opposite -- then prediction must fail somewhere.
-/

/-- Abstract diagonal lemma: if some machine `d` outputs the negation of its own
self-prediction, then self-prediction is not always correct. -/

theorem not_exists_correct_self_predictor :
    ¬ ∃ p : ℕ → ℕ, Computable p ∧
      ∀ c : Code, eval c (Nat.Partrec.Code.encodeCode c)
        = Part.some (p (Nat.Partrec.Code.encodeCode c)) := by
  rintro ⟨p, hp, hcorrect⟩
  obtain ⟨c, hc⟩ := self_nonprediction p hp
  exact hc (hcorrect c)

end Frontier

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

