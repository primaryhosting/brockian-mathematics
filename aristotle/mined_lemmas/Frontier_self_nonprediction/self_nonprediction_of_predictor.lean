/-!
# Self Nonprediction
Category: Frontier Mind
Target: Frontier.self_nonprediction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-!
## Setup

We model a family of machines `M`, each of which, when run, produces an output
`output m : α`, and which, *before* producing it, announces a prediction
`predict m : α` of that very output.

The only assumption needed is *diagonal universality*: the machine family is
rich enough to contain, for a given transformation `g : α → α`, a machine whose
output is `g` applied to its own announced prediction.  (Think of the machine
that reads off its own prediction and then deliberately does something else.)
If `g` has no fixed point — e.g. `Bool.not`, which is fixed-point-free by the
Mathlib lemma `Bool.not_ne_self` — then the prediction mechanism must fail
somewhere.

This is the classical diagonal argument; the same fixed-point-free-map core
underlies `Function.cantor_surjective` in Mathlib.  (The file is kept
import-free so that the required header comment can be the first thing in it;
everything used below is available in Lean core.)
-/

/-- **Self nonprediction.**  If a machine family contains a diagonal machine `m`
whose output is `g (predict m)` for some fixed-point-free `g`, then the
predictions cannot all be correct: no machine can always correctly predict its
own next output before producing it. -/

theorem self_nonprediction_of_predictor (P : (Bool → Bool) → Bool) :
    ¬ ∀ f : Bool → Bool, P f = f (P f) :=
  self_nonprediction_bool (M := Bool → Bool) (fun f => f (P f)) (fun f => P f)
    ⟨fun b => !b, rfl⟩

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

