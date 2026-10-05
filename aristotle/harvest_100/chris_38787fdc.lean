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
def DiagonalClosed {Code Out : Type*} (run : Code → Code → Out) (spite : Out → Out) :
    Prop := ∀ e : Code, ∃ e' : Code, ∀ x : Code, run e' x = spite (run e x)

/-- `p` predicts, for every machine description `e`, the output of `e` on `e`;
in particular (taking `e := p`) it predicts its own next output before producing it. -/
def PredictsSelfApplication {Code Out : Type*} (run : Code → Code → Out) (p : Code) :
    Prop := ∀ e : Code, run p e = run e e

/-- **Abstract diagonal argument.**  In any machine model that is closed under
diagonalization against a spiteful output transformation, no machine correctly
predicts the self-application behaviour of all machines — in particular no machine
can always correctly predict its own next output before producing it. -/
theorem no_self_predictor {Code Out : Type*} (run : Code → Code → Out)
    (spite : Out → Out) (hspite : Spiteful spite)
    (hclosed : DiagonalClosed run spite) (p : Code) :
    ¬ PredictsSelfApplication run p := by
  intro hp
  obtain ⟨d, hd⟩ := hclosed p
  -- `d` runs `p` and then outputs something different.
  have h1 : run d d = spite (run p d) := hd d
  -- but `p` claims to predict the output of `d` on `d`.
  have h2 : run p d = run d d := hp d
  rw [h2] at h1
  exact hspite (run d d) h1.symm

/-- **Self nonprediction (base case).**
No machine can always correctly predict its own next output before producing it.

Concretely: machines are coded by natural numbers, outputs are bits, and the model
is assumed only to be closed under bit-flipping the output of a given machine.
Then for every machine `p` there is a machine description `e` on which `p`'s
prediction is wrong; taking the diagonal machine built from `p`, the failure is
genuinely one of self-prediction. -/
theorem self_nonprediction (run : ℕ → ℕ → Bool)
    (hclosed : ∀ e : ℕ, ∃ e' : ℕ, ∀ x : ℕ, run e' x = !(run e x)) :
    ∀ p : ℕ, ∃ e : ℕ, run p e ≠ run e e := by
  intro p
  by_contra hcon
  push_neg at hcon
  exact no_self_predictor run (fun b => !b) (by intro b; cases b <;> simp)
    hclosed p hcon

/-- Sharper form: the machine on which the prediction fails is the machine that
consults `p`'s prediction about itself and then does the opposite.  Its own next
output is therefore not predicted by `p`. -/
theorem self_nonprediction_diagonal (run : ℕ → ℕ → Bool)
    (hclosed : ∀ e : ℕ, ∃ e' : ℕ, ∀ x : ℕ, run e' x = !(run e x)) (p : ℕ) :
    ∃ d : ℕ, (∀ x : ℕ, run d x = !(run p x)) ∧ run p d ≠ run d d := by
  obtain ⟨d, hd⟩ := hclosed p
  refine ⟨d, hd, ?_⟩
  intro h
  have : run d d = !(run p d) := hd d
  rw [← h] at this
  simp at this

/-- The hypotheses are not vacuous: there is a machine model closed under
output-flipping.  (Pair up codes `2n` and `2n+1`, letting `2n+1` be the flip of
`2n` and vice versa.) -/
theorem exists_diagonalizable :
    ∃ run : ℕ → ℕ → Bool, ∀ e : ℕ, ∃ e' : ℕ, ∀ x : ℕ, run e' x = !(run e x) := by
  refine ⟨fun e _ => decide (e % 2 = 1), ?_⟩
  intro e
  rcases Nat.even_or_odd e with he | he
  · refine ⟨e + 1, fun _ => ?_⟩
    have h0 : e % 2 = 0 := Nat.even_iff.mp he
    have h1 : (e + 1) % 2 = 1 := by omega
    simp [h0, h1]
  · refine ⟨e - 1, fun _ => ?_⟩
    have h1 : e % 2 = 1 := Nat.odd_iff.mp he
    have h0 : (e - 1) % 2 = 0 := by omega
    simp [h0, h1]

end Frontier

