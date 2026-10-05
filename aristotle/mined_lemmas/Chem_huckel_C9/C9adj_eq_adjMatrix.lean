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

lemma C9adj_eq_adjMatrix : C9adj = (SimpleGraph.cycleGraph 9).adjMatrix ℂ := by
  have key : ∀ i j : ZMod 9, (i - j = 1 ∨ i - j = -1) ↔ (i - j = 1 ∨ j - i = 1) := by
    intro i j
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linear_combination -h)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linear_combination -h)
  funext i j
  simp only [C9adj, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj]
  congr 1
  exact propext (key i j)

