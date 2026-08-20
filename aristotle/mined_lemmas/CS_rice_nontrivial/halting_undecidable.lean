import Mathlib

/-!
# Rice Nontrivial
Category: Computer Science
Target: CS.rice_nontrivial
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace CS

open Nat.Partrec Nat.Partrec.Code ComputablePred

/-- A property `P` of programs (codes) is *semantic* (extensional) when it depends only on the
partial function the program computes. -/

theorem halting_undecidable (n : ℕ) : ¬ ComputablePred fun c : Code => (eval c n).Dom := by
  refine rice_nontrivial _ (fun cf cg h => by rw [h]) ⟨⟨Code.zero, ?_⟩, ⟨?_, ?_⟩⟩
  · exact trivial
  · exact (exists_code.1 Nat.Partrec.none).choose
  · have h := (exists_code.1 Nat.Partrec.none).choose_spec
    simp [h]

end CS

