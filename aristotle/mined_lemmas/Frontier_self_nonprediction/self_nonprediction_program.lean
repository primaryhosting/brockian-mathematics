/-!
# Self Nonprediction
Category: Frontier Mind
Target: Frontier.self_nonprediction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option autoImplicit false

universe u

namespace Frontier

/-- **Self nonprediction (diagonal self-reference).**

A machine model is given by a type `M` of machines, an output function
`out : M → Bool → Bool` (the machine `m` produces the output `out m b` in the run in which
the prediction issued about it was `b` — so a machine is allowed to consult the prediction
made about its own next output), and a self-prediction function `predict : M → Bool`
(the prediction that `m` issues about its own next output, *before* producing it).

If the machine model is rich enough to contain the *diagonal* machine, i.e. one that outputs
the negation of the prediction made about it, then the self-prediction cannot always be
correct: some machine of the model fails to predict its own next output. -/

theorem self_nonprediction_program (P : (Bool → Bool) → Bool) :
    ∃ p : Bool → Bool, p (P p) ≠ P p :=
  self_nonprediction (M := Bool → Bool) (fun p b => p b) P ⟨fun b => !b, fun _ => rfl⟩

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

