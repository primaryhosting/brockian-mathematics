/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- The index set of a semantic property `P` of partial functions: the set of natural
numbers `n` such that the partial recursive function computed by the `n`-th code
satisfies `P`. -/

theorem rice_extended (P : (ℕ →. ℕ) → Prop) {f g : ℕ →. ℕ}
    (hf : Nat.Partrec f) (hg : Nat.Partrec g) (hfP : P f) (hgP : ¬ P g) :
    ¬ ComputablePred fun n : ℕ => n ∈ indexSet P := by
  intro h
  exact hgP (rice_codes (computablePred_code_of_indexSet h) hf hg hfP)

/-- Every code evaluates to a partial recursive function. -/
