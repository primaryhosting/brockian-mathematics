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

theorem exists_machine_defeating_predictor_bool (P : (Bool → Bool) → Bool) :
    ∃ f : Bool → Bool, f (P f) ≠ P f :=
  exists_machine_defeating_predictor (fun b => !b) bool_not_ne_self P

/-- The target statement with the diagonalization hypothesis discharged: in the
machine model `M = Bool → Bool`, where `output f = f (P f)` is what the machine
actually produces and `predict f = P f` is what was announced beforehand, no
predictor `P` is correct on all machines. -/
