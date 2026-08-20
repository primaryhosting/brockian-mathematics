/-
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset

namespace CS

/-! ## Boolean strings, probabilities and majority votes -/

/-- Boolean strings of length `n`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- The probability that the test `T` accepts a uniformly random string of length `k`. -/

def trivialModel : Model where
  Poly := fun _ => True
  EffRand := fun A => ∀ n, A.len n ≤ Nat.log 2 (n + 1)
  ExpTime := fun _ => True
  EffPRG := fun _ => True
  det_mem_rand := by
    intro L _
    refine ⟨⟨fun _ => 0, fun n x _ => L n x⟩, fun n => Nat.zero_le _, ?_⟩
    intro n x
    constructor
    · intro h
      simp only [h]
      rw [prob_const_true]
      norm_num
    · intro h
      simp only [h]
      rw [prob_const_false]
      norm_num
  derandomize_poly := by intro _ _ _ _; trivial

