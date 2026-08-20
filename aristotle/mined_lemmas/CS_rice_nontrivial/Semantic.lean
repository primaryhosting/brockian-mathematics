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

def Semantic (P : Code → Prop) : Prop :=
  ∀ cf cg : Code, eval cf = eval cg → (P cf ↔ P cg)

/-- A property `P` of programs is *nontrivial* when some program satisfies it and some
program does not. -/
