import Mathlib
/-!
# Self Nonprediction
Category: Frontier Mind
Target: Frontier.self_nonprediction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

/-!
## The abstract diagonal argument

A "self-prediction system" is a collection `M` of machines, where `out m` is the next
output of machine `m` and `pred m` is the prediction that machine `m` makes about that
output *before* producing it.  If the collection is closed under diagonalization -- i.e.
it contains a machine that first consults its own prediction and then outputs the
opposite -- then prediction must fail somewhere.
-/

/-- Abstract diagonal lemma: if some machine `d` outputs the negation of its own
self-prediction, then self-prediction is not always correct. -/
theorem exists_prediction_failure {M : Type*} (out pred : M → Bool)
    (hdiag : ∃ d : M, out d = !(pred d)) : ∃ m : M, pred m ≠ out m := by
  obtain ⟨d, hd⟩ := hdiag
  exact ⟨d, by simp [hd]⟩

/-- Contrapositive form: no self-prediction scheme is correct on all machines, as soon
as the diagonal (contrarian) machine is available. -/
theorem not_forall_self_prediction_correct {M : Type*} (out pred : M → Bool)
    (hdiag : ∃ d : M, out d = !(pred d)) : ¬ ∀ m : M, pred m = out m := by
  obtain ⟨m, hm⟩ := exists_prediction_failure out pred hdiag
  exact fun h => hm (h m)

/-!
## The concrete computability-theoretic version

Here machines are actual programs (`Nat.Partrec.Code`), a machine `c` is run on its own
code `encodeCode c`, and its next output is `eval c (encodeCode c)`.  A *predictor* is any
total computable function `p : ℕ → ℕ` which, given the code of a machine, is supposed to
announce that machine's output on its own code.

The diagonal machine is the program which, on input `x`, runs the predictor on `x` and
outputs `p x + 1`: run on its own code it consults the prediction made about itself and
then produces something different.
-/

/-- **Self nonprediction.**  No machine can always correctly predict its own next output
before producing it: for every total computable predictor `p`, there is a program `c`
whose output on its own code differs from the prediction `p` makes about it.  The witness
`c` is precisely the machine that computes its own predicted output and then outputs
something else. -/
theorem self_nonprediction (p : ℕ → ℕ) (hp : Computable p) :
    ∃ c : Code, eval c (Nat.Partrec.Code.encodeCode c)
      ≠ Part.some (p (Nat.Partrec.Code.encodeCode c)) := by
  have hpart : Nat.Partrec (fun x => (Part.some (p x + 1))) := by
    rw [← Partrec.nat_iff]
    exact (Computable.succ.comp hp).partrec
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hpart
  refine ⟨c, ?_⟩
  rw [hc]
  simp

/-- Contrapositive packaging of `self_nonprediction`: no total computable predictor is
correct about every machine's output on its own code. -/
theorem not_exists_correct_self_predictor :
    ¬ ∃ p : ℕ → ℕ, Computable p ∧
      ∀ c : Code, eval c (Nat.Partrec.Code.encodeCode c)
        = Part.some (p (Nat.Partrec.Code.encodeCode c)) := by
  rintro ⟨p, hp, hcorrect⟩
  obtain ⟨c, hc⟩ := self_nonprediction p hp
  exact hc (hcorrect c)

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

