/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Chem

/-- A primitive fifth root of unity. -/

lemma C5adj_isSymm : C5adj.IsSymm := by
  ext i j
  have h : (j = i + 1 ∨ j = i - 1) ↔ (i = j + 1 ∨ i = j - 1) := by
    constructor <;> rintro (h | h) <;> subst h
    · exact Or.inr (by ring)
    · exact Or.inl (by ring)
    · exact Or.inr (by ring)
    · exact Or.inl (by ring)
  simp only [Matrix.transpose_apply, C5adj]
  exact if_congr h.symm rfl rfl

/-! ### Basic facts about `ζ₅` -/

