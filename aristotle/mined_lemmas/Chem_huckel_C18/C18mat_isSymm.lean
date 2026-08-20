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

theorem C18mat_isSymm : C18mat.IsSymm := by
  ext i j
  rw [Matrix.transpose_apply, C18mat_apply, C18mat_apply]
  have e : (i = j - 1 ∨ i = j + 1) ↔ (j = i - 1 ∨ j = i + 1) := by
    constructor <;> rintro (h | h)
    · exact Or.inr (by linear_combination -h)
    · exact Or.inl (by linear_combination -h)
    · exact Or.inr (by linear_combination -h)
    · exact Or.inl (by linear_combination -h)
  simp only [e]

