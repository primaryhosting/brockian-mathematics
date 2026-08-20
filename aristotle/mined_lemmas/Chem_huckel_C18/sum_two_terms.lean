/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Polynomial Finset

noncomputable section

/-- A primitive 18-th root of unity. -/

theorem sum_two_terms (g : ZMod 18 → ℂ) (j : ZMod 18) :
    ∑ l : ZMod 18, (if j - l = 1 ∨ j - l = -1 then (1 : ℂ) else 0) * g l
      = g (j - 1) + g (j + 1) := by
  have hne : (j - 1 : ZMod 18) ≠ j + 1 := by
    intro h
    have : (2 : ZMod 18) = 0 := by linear_combination -h
    exact absurd this (by decide)
  have key : ∀ l : ZMod 18,
      (if j - l = 1 ∨ j - l = -1 then (1 : ℂ) else 0) * g l
        = (if l = j - 1 then g l else 0) + (if l = j + 1 then g l else 0) := by
    intro l
    have e1 : (j - l = 1) ↔ l = j - 1 := by
      constructor <;> intro h <;> linear_combination -h
    have e2 : (j - l = -1) ↔ l = j + 1 := by
      constructor <;> intro h <;> linear_combination -h
    simp only [e1, e2]
    by_cases h1 : l = j - 1 <;> by_cases h2 : l = j + 1
    · exact absurd (h1 ▸ h2) hne
    · simp [h1, hne]
    · simp [h2, Ne.symm hne]
    · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun l _ => key l), Finset.sum_add_distrib]
  simp

