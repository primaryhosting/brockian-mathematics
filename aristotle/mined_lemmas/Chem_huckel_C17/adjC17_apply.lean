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

lemma adjC17_apply (i j : ZMod 17) :
    adjC17 i j = if j = i - 1 ∨ j = i + 1 then 1 else 0 := by
  have hiff : (i - j = 1 ∨ j - i = 1) ↔ (j = i - 1 ∨ j = i + 1) := by
    constructor
    · rintro (h | h)
      · exact Or.inl (by linear_combination -h)
      · exact Or.inr (by linear_combination h)
    · rintro (h | h)
      · exact Or.inl (by linear_combination -h)
      · exact Or.inr (by linear_combination h)
  simp only [adjC17, Matrix.of_apply, hiff]

