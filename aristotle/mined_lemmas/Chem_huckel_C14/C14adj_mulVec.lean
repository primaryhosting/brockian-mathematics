import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex SimpleGraph

namespace Chem

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₁₄`, i.e. the Hückel matrix of the
carbon skeleton of a 14-membered annulene in units where `α = 0` and `β = 1`. -/

private lemma C14adj_mulVec (v : Fin 14 → ℂ) (i : Fin 14) :
    C14adj.mulVec v i = v (i - 1) + v (i + 1) := by
  have hne : i - 1 ≠ i + 1 := by revert i; decide
  rw [C14adj, SimpleGraph.adjMatrix_mulVec_apply]
  rw [show (14 : ℕ) = 12 + 2 from rfl] at *
  rw [SimpleGraph.cycleGraph_neighborFinset, Finset.sum_pair hne]

/-- The same statement, with the index set `Fin 14` viewed as the additive group `ZMod 14`. -/
