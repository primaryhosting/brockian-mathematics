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
def IsSelfPredictor {Program : Type u} (eval : Program → Bool → Bool)
    (P : Program → Bool) : Prop :=
  ∀ e : Program, P e = eval e (P e)

/-- `HasContrarian eval` says the machine model contains a machine that outputs the
negation of the prediction announced for it. -/
def HasContrarian {Program : Type u} (eval : Program → Bool → Bool) : Prop :=
  ∃ c : Program, ∀ b : Bool, eval c b = !b

/-!
## The diagonal argument
-/

/-- A contrarian machine defeats every candidate self-predictor: on it, the announced
prediction is provably wrong. -/
theorem contrarian_defeats_predictor {Program : Type u} (eval : Program → Bool → Bool)
    {c : Program} (hc : ∀ b : Bool, eval c b = !b) (P : Program → Bool) :
    P c ≠ eval c (P c) := by
  rw [hc (P c)]
  cases P c <;> simp

/-- **Self nonprediction (witness form).** For every candidate self-predictor `P` there is
an explicit machine on which the prediction, announced before the output is produced,
is wrong. -/
theorem exists_self_nonprediction {Program : Type u} (eval : Program → Bool → Bool)
    (hcon : HasContrarian eval) (P : Program → Bool) :
    ∃ e : Program, P e ≠ eval e (P e) := by
  obtain ⟨c, hc⟩ := hcon
  exact ⟨c, contrarian_defeats_predictor eval hc P⟩

/-- **Self nonprediction.**  No machine can always correctly predict its own next output
before producing it: in any machine model containing a contrarian machine, no map `P`
assigning to each machine a prediction of its next output bit — a prediction made
available to the machine before it produces that bit — can always be correct. -/
theorem self_nonprediction {Program : Type u} (eval : Program → Bool → Bool)
    (hcon : HasContrarian eval) (P : Program → Bool) :
    ¬ IsSelfPredictor eval P := by
  intro hP
  obtain ⟨e, he⟩ := exists_self_nonprediction eval hcon P
  exact he (hP e)

/-!
## Unconditional concrete instances

Taking the machines to *be* their input–output behaviours, the richness hypothesis is
discharged and the result becomes assumption-free.
-/

/-- The concrete machine model whose machines are the Boolean behaviours `Bool → Bool`
contains a contrarian machine. -/
theorem hasContrarian_id : HasContrarian (fun f : Bool → Bool => f) :=
  ⟨fun b => !b, fun _ => rfl⟩

/-- **Self nonprediction, unconditional concrete form.**  There is no function `P`
assigning to each Boolean behaviour `f` a prediction `P f` of the bit `f` outputs when
handed that very prediction. -/
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
theorem self_nonprediction_indexed (run : Nat → Bool → Bool) (c : Nat)
    (hc : ∀ b : Bool, run c b = !b) (P : Nat → Bool) :
    ¬ ∀ e : Nat, P e = run e (P e) :=
  self_nonprediction run ⟨c, hc⟩ P

end Frontier

-- Axiom audit: each result depends only on `propext` (no `sorry`, no classical choice).
#print axioms Frontier.self_nonprediction
#print axioms Frontier.exists_self_nonprediction
#print axioms Frontier.self_nonprediction_concrete
#print axioms Frontier.self_nonprediction_indexed

