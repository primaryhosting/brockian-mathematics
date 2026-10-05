import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- A primitive ninth root of unity. -/

lemma mulVec_apply (v : ZMod 9 → ℂ) (i : ZMod 9) :
    C9adj.mulVec v i = v (i - 1) + v (i + 1) := by
  have hne : (i - 1 : ZMod 9) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 9) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have key : ∀ j : ZMod 9, C9adj i j * v j
      = (if j = i - 1 then v j else 0) + (if j = i + 1 then v j else 0) := by
    intro j
    have e1 : (i - j = 1) ↔ j = i - 1 := by
      constructor
      · intro h; linear_combination -h
      · intro h; rw [h]; ring
    have e2 : (i - j = -1) ↔ j = i + 1 := by
      constructor
      · intro h; linear_combination -h
      · intro h; rw [h]; ring
    simp only [C9adj, e1, e2]
    by_cases h1 : j = i - 1
    · simp [h1, hne]
    · by_cases h2 : j = i + 1 <;> simp [h1, h2, hne.symm]
  rw [Matrix.mulVec, dotProduct]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ]
  simp

