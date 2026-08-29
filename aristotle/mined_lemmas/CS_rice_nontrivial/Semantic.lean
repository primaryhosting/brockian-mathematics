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

def Semantic (C : Set Code) : Prop :=
  ∀ c₁ c₂ : Code, eval c₁ = eval c₂ → (c₁ ∈ C ↔ c₂ ∈ C)

/-- A property `C` of programs is *nontrivial* if some program has it and some program lacks it. -/
