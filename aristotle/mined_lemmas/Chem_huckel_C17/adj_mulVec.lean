/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open scoped Real
open Finset

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- A primitive 17-th root of unity. -/

lemma adj_mulVec (f : ZMod 17 → ℂ) (i : ZMod 17) :
    adjC17.mulVec f i = f (i - 1) + f (i + 1) := by
  have hne : (i - 1 : ZMod 17) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 17) = 0 := by linear_combination -h
    revert h2; decide
  have key : ∀ j : ZMod 17, adjC17 i j * f j
      = (if j = i - 1 then f j else 0) + (if j = i + 1 then f j else 0) := by
    intro j
    rw [adjC17_apply]
    by_cases hA : j = i - 1
    · have hB : j ≠ i + 1 := by rw [hA]; exact hne
      simp [hA, hne]
    · by_cases hB : j = i + 1
      · simp [hB, Ne.symm hne]
      · simp [hA, hB]
  simp only [Matrix.mulVec, dotProduct, key]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (i - 1) f,
    Finset.sum_ite_eq' Finset.univ (i + 1) f]
  simp

