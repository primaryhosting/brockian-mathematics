/-!
# Self Nonprediction
Category: Frontier Mind
Target: Frontier.self_nonprediction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- No `import` is needed: the development uses only `Bool`, `Nat` and core tactics.
-- (An `import` line may not precede the required header comment above.)

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Frontier

/-!
## Setup

We model a *machine model* abstractly.  `Program` is the type of machines.  A machine is
run *after* it has been handed a prediction of the bit it is about to emit: `eval e b` is
the next output bit of machine `e` when the bit `b` has been announced (before the
output is produced) as the prediction of that very output.  This is exactly the
"predict its own next output *before* producing it" situation: the prediction is
available to the machine at the moment it computes the output.

A *self-predictor* for the model is a map `P : Program → Bool`, where `P e` is the bit
announced as the prediction for `e`; it is *always correct* when

  `∀ e, P e = eval e (P e)`.

The only assumption on the machine model is that it is closed under the trivial
"contrarian" behaviour: some machine simply negates the bit it was handed.  Every
reasonable machine model (Turing machines, circuits, λ-terms, ...) satisfies this, and
below we also give unconditional concrete instances.
-/

/-- `IsSelfPredictor eval P` says that the prediction `P e`, announced before machine `e`
produces its next output bit, always agrees with that bit. -/

theorem self_nonprediction_concrete (P : (Bool → Bool) → Bool) :
    ¬ ∀ f : Bool → Bool, P f = f (P f) :=
  self_nonprediction (fun f : Bool → Bool => f) hasContrarian_id P

/-!
## Indexed (Gödel-numbered) form

The usual presentation: machines are numbered by `Nat` and `run e b` is the next output
bit of machine number `e` after the prediction `b` has been announced.  If the numbering
covers the contrarian machine — the mildest possible richness requirement — then no
total predictor `P : Nat → Bool` is always right.
-/

/-- **Self nonprediction, Gödel-numbered form.** -/
