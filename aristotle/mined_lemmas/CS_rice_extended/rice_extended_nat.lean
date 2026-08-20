/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Statement: The set of indices of a nontrivial semantic property is not recursive (Rice).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
/-!
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Statement: The set of indices of a nontrivial semantic property is not recursive (Rice).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped Classical

set_option maxHeartbeats 1000000

namespace CS

open Nat.Partrec Nat.Partrec.Code ComputablePred

/-- The index set of a property `P` of partial functions: the set of (codes of) programs
whose computed partial function has the property `P`. -/

theorem rice_extended_nat (P : Set (ℕ →. ℕ)) (hP : Nontrivial P) :
    ¬ ComputablePred (fun n : ℕ => n ∈ natIndexSet P) := by
  intro h
  refine rice_extended P hP ?_
  have : ComputablePred fun c : Nat.Partrec.Code => (Encodable.encode c) ∈ natIndexSet P :=
    ComputablePred.computable_iff.2 <| by
      obtain ⟨_, hc⟩ := h
      exact ⟨_, hc.comp Computable.encode, by
        funext c; simp [natIndexSet]⟩
  refine this.of_eq fun c => ?_
  simp [natIndexSet, indexSet, Denumerable.ofNat_encode]

end CS

