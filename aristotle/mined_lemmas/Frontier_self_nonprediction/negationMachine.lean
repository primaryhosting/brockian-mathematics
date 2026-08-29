/-!
# Self Nonprediction
Category: Frontier Mind
Target: Frontier.self_nonprediction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A `PredictiveMachine` is an abstract model of a family of machines:
`M` is the type of machine configurations, `output c` is the (boolean) output the
machine eventually produces from configuration `c`, and `predict c` is the
prediction, issued *before* producing the output, of what that output will be.

The field `diag` is the diagonal (self-referential) configuration: a machine that
first consults its own prediction and then outputs the opposite bit.  Its
defining property is `output_diag`. -/
structure PredictiveMachine where
  /-- Type of machine configurations. -/
  M : Type
  /-- The output eventually produced from a configuration. -/
  output : M → Bool
  /-- The prediction issued before producing the output. -/
  predict : M → Bool
  /-- The diagonal configuration: it negates its own prediction. -/
  diag : M
  /-- Defining property of the diagonal configuration. -/
  output_diag : output diag = !predict diag

/-- **Self nonprediction.**  No machine can always correctly predict its own next
output before producing it: as soon as the machine is powerful enough to contain
the diagonal configuration (one that reads off its own prediction and outputs the
opposite bit), the prediction must fail on some configuration. -/

def negationMachine : PredictiveMachine where
  M := Bool
  output b := !b
  predict b := b
  diag := true
  output_diag := rfl

example : ¬ ∀ c : negationMachine.M, negationMachine.predict c = negationMachine.output c :=
  self_nonprediction negationMachine

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

