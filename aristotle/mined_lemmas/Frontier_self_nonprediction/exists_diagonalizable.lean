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

