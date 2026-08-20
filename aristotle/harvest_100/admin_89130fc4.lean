/-!
# Self Nonprediction
Category: Frontier Mind
Target: Frontier.self_nonprediction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Setting

We model a family of machines by a type `M` together with two observables:

* `pred m : Bool` — the prediction machine `m` makes about its own next output,
  issued *before* the output is produced;
* `out m : Bool` — the output machine `m` actually produces.

The only structural assumption is a *self-reference* (recursion-theorem style) principle:
for every post-processing `f : Bool → Bool` there is a machine in the family whose output
is `f` applied to its own prediction.  This is exactly the ability, guaranteed by Kleene's
recursion theorem in any reasonable programming formalism, to build a machine that reads
off its own prediction and then acts on it.

The diagonal argument then shows prediction must fail somewhere: taking `f = not` yields a
machine that outputs the negation of its own forecast.  The diagonal step is the two-element
instance of Cantor's argument (`!b ≠ b`, in Mathlib `Bool.not_ne_self`); it is proved here by
`decide` so that the file has no dependencies beyond core Lean.
-/

namespace Frontier

/-- The diagonal step: a Boolean never equals its negation.
(Mathlib states this as `Bool.not_ne_self`.) -/
theorem bool_not_ne_self (b : Bool) : b ≠ !b := by
  cases b <;> decide

/-- **Self-nonprediction.**  In any machine family closed under self-reference
(`hself`: for every `f : Bool → Bool` some machine outputs `f` of its own prediction),
self-prediction cannot always be correct: there is a machine whose announced prediction
differs from the output it goes on to produce. -/
theorem self_nonprediction {M : Type u} (pred out : M → Bool)
    (hself : ∀ f : Bool → Bool, ∃ m : M, out m = f (pred m)) :
    ∃ m : M, pred m ≠ out m := by
  obtain ⟨m, hm⟩ := hself (fun b => !b)
  refine ⟨m, ?_⟩
  rw [hm]
  exact bool_not_ne_self (pred m)

/-- Contrapositive form: an always-correct self-predictor is impossible. -/
theorem no_correct_self_predictor {M : Type u} (pred out : M → Bool)
    (hself : ∀ f : Bool → Bool, ∃ m : M, out m = f (pred m)) :
    ¬ ∀ m : M, pred m = out m := by
  obtain ⟨m, hm⟩ := self_nonprediction pred out hself
  exact fun h => hm (h m)

/-!
## Non-vacuity

The self-reference hypothesis is satisfiable: take a machine to be a pair
`(prediction, output)`; a machine computing its output as `f` of its own prediction is
then simply the pair `(b, f b)`.
-/

/-- The hypotheses of `Frontier.self_nonprediction` are satisfiable: the family of all
`(prediction, output)` pairs is closed under self-reference. -/
theorem self_reference_example :
    ∀ f : Bool → Bool, ∃ m : Bool × Bool, (fun p => p.2) m = f ((fun p => p.1) m) :=
  fun f => ⟨(true, f true), rfl⟩

/-- Instantiating the theorem on that family: some machine mispredicts itself. -/
example : ∃ m : Bool × Bool, m.1 ≠ m.2 :=
  self_nonprediction (fun p : Bool × Bool => p.1) (fun p : Bool × Bool => p.2)
    self_reference_example

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

