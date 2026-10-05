/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Chem

open Finset Complex

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- A primitive 7-th root of unity. -/

lemma mulVec_C7adj (v : ZMod 7 → ℂ) (i : ZMod 7) :
    C7adj.mulVec v i = v (i - 1) + v (i + 1) := by
  have hne : (i - 1 : ZMod 7) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 7) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have hterm : ∀ j : ZMod 7, C7adj i j * v j
      = (if j = i - 1 then v j else 0) + (if j = i + 1 then v j else 0) := by
    intro j
    simp only [C7adj]
    by_cases h1 : j = i - 1
    · have hij : i - j = 1 := by rw [h1]; ring
      have h2 : j ≠ i + 1 := by rw [h1]; exact hne
      rw [hij, if_pos (Or.inl rfl), if_pos h1, if_neg h2, one_mul, add_zero]
    · by_cases h2 : j = i + 1
      · have hij : i - j = -1 := by rw [h2]; ring
        rw [hij, if_pos (Or.inr rfl), if_neg h1, if_pos h2, one_mul, zero_add]
      · have hz : ¬ (i - j = 1 ∨ i - j = -1) := by
          rintro (h | h)
          · exact h1 (by linear_combination -h)
          · exact h2 (by linear_combination -h)
        rw [if_neg hz, if_neg h1, if_neg h2, zero_mul, add_zero]
  simp only [Matrix.mulVec, dotProduct, hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (i - 1) v,
    Finset.sum_ite_eq' Finset.univ (i + 1) v]
  simp

/-- The `k`-th Fourier eigenvector. -/
