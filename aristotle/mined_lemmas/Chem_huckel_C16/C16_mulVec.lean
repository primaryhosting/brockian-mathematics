/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Finset

/-- A primitive 16-th root of unity. -/

lemma C16_mulVec (v : ZMod 16 → ℂ) (i : ZMod 16) :
    C16.mulVec v i = v (i - 1) + v (i + 1) := by
  have hne : (i - 1 : ZMod 16) ≠ i + 1 := by
    intro h
    have : (2 : ZMod 16) = 0 := by linear_combination -h
    exact absurd this (by decide)
  have hterm : ∀ j : ZMod 16, C16 i j * v j
      = if j ∈ ({i - 1, i + 1} : Finset (ZMod 16)) then v j else 0 := by
    intro j
    have h1 : (i - j = 1) ↔ j = i - 1 := by
      constructor <;> intro h <;> linear_combination -h
    have h2 : (i - j = -1) ↔ j = i + 1 := by
      constructor <;> intro h <;> linear_combination -h
    simp only [C16, h1, h2, Finset.mem_insert, Finset.mem_singleton]
    split <;> simp_all
  rw [Matrix.mulVec, dotProduct]
  simp only [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair hne]

