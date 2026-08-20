/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- A primitive 11-th root of unity. -/

lemma mulVec_C11 (v : ZMod 11 → ℂ) (i : ZMod 11) :
    C11.mulVec v i = v (i + 1) + v (i - 1) := by
  have hne : (i + 1 : ZMod 11) ≠ i - 1 := by
    intro h
    have : (2 : ZMod 11) = 0 := by linear_combination h
    exact absurd this (by decide)
  have : C11.mulVec v i = ∑ j ∈ ({i + 1, i - 1} : Finset (ZMod 11)), v j := by
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_congr rfl (g := fun j => if j ∈ ({i + 1, i - 1} : Finset (ZMod 11)) then v j else 0)]
    · rw [Finset.sum_ite_mem, Finset.univ_inter]
    · intro j _
      by_cases h : j = i + 1 ∨ j = i - 1 <;> simp [C11, h]
  rw [this, Finset.sum_pair hne]

