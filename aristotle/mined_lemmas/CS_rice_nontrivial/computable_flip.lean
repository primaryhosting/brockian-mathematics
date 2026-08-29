import Mathlib

/-!
# Rice Nontrivial
Category: Computer Science
Target: CS.rice_nontrivial
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

open scoped Classical

/-- A property `C` of programs (codes) is *semantic* (extensional) if it depends only on the
partial function the program computes. -/

theorem computable_flip {C : Set Code} (h : ComputablePred fun c => c ∈ C) (a b : Code) :
    Computable fun c => if c ∈ C then a else b := by
  obtain ⟨_, hc⟩ := h
  refine (Computable.cond hc (Computable.const a) (Computable.const b)).of_eq fun c => ?_
  by_cases hcC : c ∈ C <;> simp [hcC]

/-- **Rice's theorem.** Every nontrivial semantic property of programs is undecidable. -/
