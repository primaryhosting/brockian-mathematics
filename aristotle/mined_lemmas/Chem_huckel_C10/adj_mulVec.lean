import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real Matrix Finset

namespace Chem

/-- A primitive 10-th root of unity. -/

theorem adj_mulVec (v : ZMod 10 → ℂ) (i : ZMod 10) :
    (C10adj *ᵥ v) i = v (i - 1) + v (i + 1) := by
  have hne : (i - 1 : ZMod 10) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 10) = 0 := by linear_combination -h
    revert h2; decide
  have h : ∀ j : ZMod 10, C10adj i j * v j
      = (if j = i - 1 then v j else 0) + (if j = i + 1 then v j else 0) := by
    intro j
    have h1 : (i - j = 1) ↔ j = i - 1 := by
      constructor
      · intro h; rw [← h]; ring
      · intro h; rw [h]; ring
    have h2 : (j - i = 1) ↔ j = i + 1 := by
      constructor
      · intro h; rw [← h]; ring
      · intro h; rw [h]; ring
    by_cases hA : j = i - 1 <;> by_cases hB : j = i + 1
    · exact absurd (hA.symm.trans hB) hne
    · simp [C10adj, hA, hne]
    · simp [C10adj, hB, hne.symm]
    · simp [C10adj, h1, h2, hA, hB]
  rw [Matrix.mulVec, dotProduct]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ]
  simp

