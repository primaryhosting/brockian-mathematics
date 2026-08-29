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
