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
