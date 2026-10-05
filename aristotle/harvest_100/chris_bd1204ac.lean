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
theorem self_nonprediction (P : PredictiveMachine) :
    ¬ ∀ c : P.M, P.predict c = P.output c := by
  intro h
  have hd := P.output_diag
  rw [← h P.diag] at hd
  cases hbool : P.predict P.diag <;> simp [hbool] at hd

/-- The diagonal configuration itself is a witness to the failure of prediction. -/
theorem predict_diag_ne_output (P : PredictiveMachine) :
    P.predict P.diag ≠ P.output P.diag := by
  intro h
  rw [P.output_diag] at h
  cases hbool : P.predict P.diag <;> rw [hbool] at h <;> simp at h

/-- The hypotheses of `self_nonprediction` are satisfiable: here is a concrete
predictive machine, so the theorem is not vacuous.  Configurations are booleans
(the prediction to be issued), and the machine outputs the negation of its
prediction. -/
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

