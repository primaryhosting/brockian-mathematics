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
theorem self_nonprediction {M : Type u} {α : Type v}
    (output predict : M → α) (g : α → α) (hg : ∀ a, g a ≠ a)
    (hdiag : ∃ m, output m = g (predict m)) :
    ¬ ∀ m, predict m = output m := by
  intro h
  obtain ⟨m, hm⟩ := hdiag
  exact hg (predict m) (by rw [← hm, ← h m])

/-- `Bool.not` has no fixed point (this is Mathlib's `Bool.not_ne_self`,
reproved here to keep the file import-free). -/
theorem bool_not_ne_self : ∀ b : Bool, (!b) ≠ b := by decide

/-- The concrete base case over `Bool`: a machine that negates its own
announced prediction defeats the predictor. -/
theorem self_nonprediction_bool {M : Type u}
    (output predict : M → Bool)
    (hdiag : ∃ m, output m = !predict m) :
    ¬ ∀ m, predict m = output m :=
  self_nonprediction output predict (fun b => !b) bool_not_ne_self hdiag

/-- A fully concrete instance: a machine that announces `b` and then outputs
`!b` is never correct about itself. -/
example : ¬ ∀ b : Bool, b = !b :=
  self_nonprediction_bool (M := Bool) (fun b => !b) id ⟨true, rfl⟩

/-!
## Hypothesis-free form

In the statements above the diagonal machine is *assumed* to exist (`hdiag`).
We now discharge that assumption in a concrete model, so that the resulting
statements carry no diagonalization hypothesis at all.

Model a machine as a function `f : α → α`: it is first shown the prediction
that has been made about it, and then produces its output.  A *self-predictor*
is any function `P : (α → α) → α` announcing, for each machine `f`, the value
`P f` that `f` will output when run on that very announcement.  Correctness of
the prediction for `f` means `f (P f) = P f`.
-/

/-- **No self-predictor is always correct.**  For every predictor `P` there is
a machine `f` that outputs something different from what `P` announced for it,
namely any fixed-point-free `g`.  No hypotheses beyond the existence of a
fixed-point-free map on `α`. -/
theorem exists_machine_defeating_predictor {α : Type v} (g : α → α)
    (hg : ∀ a, g a ≠ a) (P : (α → α) → α) :
    ∃ f : α → α, f (P f) ≠ P f :=
  ⟨g, hg (P g)⟩

/-- The `Bool` case of `exists_machine_defeating_predictor`: the machine that
negates whatever was predicted of it defeats every predictor. -/
theorem exists_machine_defeating_predictor_bool (P : (Bool → Bool) → Bool) :
    ∃ f : Bool → Bool, f (P f) ≠ P f :=
  exists_machine_defeating_predictor (fun b => !b) bool_not_ne_self P

/-- The target statement with the diagonalization hypothesis discharged: in the
machine model `M = Bool → Bool`, where `output f = f (P f)` is what the machine
actually produces and `predict f = P f` is what was announced beforehand, no
predictor `P` is correct on all machines. -/
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

