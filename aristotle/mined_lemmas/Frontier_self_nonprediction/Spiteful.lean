/-
# Self Nonprediction
Category: Frontier Mind
Target: Frontier.self_nonprediction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Self Nonprediction
Category: Frontier Mind
Target: Frontier.self_nonprediction
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

namespace Frontier

/-!
## Setting

A *machine model* consists of a type `Code` of machine descriptions, a type `Out` of
possible outputs, and a semantics `run : Code → Code → Out`, where `run e x` is the
next output that machine `e` produces on input `x`.

Two mild structural assumptions are made, both of which hold in any reasonable
model of computation (and are shown to be satisfiable in `exists_diagonalizable`
below):

* `spite : Out → Out` is a *spiteful* transformation: `spite b ≠ b` for every `b`
  (with two distinct possible outputs one can always disagree with a prediction);
* the model is closed under composing a machine with `spite`: for every machine `e`
  there is a machine that runs `e` and then outputs something different.

A machine `p` is a *self-predictor* if, presented with the description of any
machine `e` (including its own), it outputs, before `e` runs, exactly the output
that `e` produces on that description. Applied to `p` itself this in particular
demands that `p` announce its own next output.
-/

/-- A transformation of outputs that always disagrees with its input. -/

def Spiteful {Out : Type*} (spite : Out → Out) : Prop := ∀ b : Out, spite b ≠ b

/-- The machine model is closed under "run `e`, then output something else". -/
