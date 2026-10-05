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

theorem predict_diag_ne_output (P : PredictiveMachine) :
    P.predict P.diag ≠ P.output P.diag := by
  intro h
  rw [P.output_diag] at h
  cases hbool : P.predict P.diag <;> rw [hbool] at h <;> simp at h

/-- The hypotheses of `self_nonprediction` are satisfiable: here is a concrete
predictive machine, so the theorem is not vacuous.  Configurations are booleans
(the prediction to be issued), and the machine outputs the negation of its
prediction. -/
