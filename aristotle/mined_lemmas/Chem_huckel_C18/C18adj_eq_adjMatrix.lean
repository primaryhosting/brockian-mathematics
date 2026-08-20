import Mathlib
/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₁₈`, with vertices indexed by `ZMod 18`:
two vertices are adjacent iff they differ by `1` modulo `18`. -/

lemma C18adj_eq_adjMatrix : C18adj = (SimpleGraph.cycleGraph 18).adjMatrix ℂ := by
  have key : ∀ i j : ZMod 18,
      ((j = i + 1 ∨ j = i - 1) ↔ (SimpleGraph.cycleGraph 18).Adj i j) := by decide
  ext i j
  simp only [C18adj, Matrix.of_apply, SimpleGraph.adjMatrix_apply]
  exact if_congr (key i j) rfl rfl

/-- The standard additive character `m ↦ exp (2πI m / 18)` on `ZMod 18`. -/
