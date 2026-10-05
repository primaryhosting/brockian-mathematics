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

theorem exists_self_nonprediction {Program : Type u} (eval : Program → Bool → Bool)
    (hcon : HasContrarian eval) (P : Program → Bool) :
    ∃ e : Program, P e ≠ eval e (P e) := by
  obtain ⟨c, hc⟩ := hcon
  exact ⟨c, contrarian_defeats_predictor eval hc P⟩

/-- **Self nonprediction.**  No machine can always correctly predict its own next output
before producing it: in any machine model containing a contrarian machine, no map `P`
assigning to each machine a prediction of its next output bit — a prediction made
available to the machine before it produces that bit — can always be correct. -/
