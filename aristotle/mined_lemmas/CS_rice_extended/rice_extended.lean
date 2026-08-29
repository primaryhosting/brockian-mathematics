/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- A set of codes is *semantic* (extensional) if membership only depends on the
partial function computed by the code. -/

theorem rice_extended (C : Set Code) (hsem : Semantic C)
    (hin : ∃ cf : Code, cf ∈ C) (hout : ∃ cg : Code, cg ∉ C) :
    ¬ ComputablePred (fun c : Code => c ∈ C) := by
  intro h
  obtain ⟨cf, hcf⟩ := hin
  obtain ⟨cg, hcg⟩ := hout
  rcases (ComputablePred.rice₂ C hsem).1 h with rfl | rfl
  · exact hcf
  · exact hcg (Set.mem_univ _)

/-- The same statement phrased for a property of partial functions: if `C` is a set of
partial functions containing the value of some code and omitting the value of some code,
then the set of codes computing a function in `C` is not decidable. -/
