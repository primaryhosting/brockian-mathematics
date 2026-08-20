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

theorem rice_nontrivial_partrec (C : Set (ℕ →. ℕ)) {f g : ℕ →. ℕ}
    (hf : Nat.Partrec f) (hg : Nat.Partrec g) (hfC : f ∈ C) (hgC : g ∉ C) :
    ¬ ComputablePred fun c => eval c ∈ C := fun h => hgC (rice C h hf hg hfC)


/-- An application: for each `n`, "the program halts on input `n`" is a nontrivial semantic
property, hence undecidable. -/
