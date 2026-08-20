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

def Nontrivial (P : Code → Prop) : Prop :=
  (∃ c : Code, P c) ∧ ∃ c : Code, ¬ P c

/-- **Rice's theorem.**  Every nontrivial semantic property of programs is undecidable. -/
