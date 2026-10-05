import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix SimpleGraph Finset

/-- The adjacency matrix of the cycle graph `C₁₃` (the Hückel matrix of the
`C₁₃` carbon ring, in units where `α = 0` and `β = 1`). -/

lemma sum_adj (f : Fin 13 → ℂ) (j : Fin 13) :
    ∑ l, C13 j l * f l = f (j - 1) + f (j + 1) := by
  have hne : (j : Fin 13) - 1 ≠ j + 1 := by revert j; decide
  have h : ∑ l, C13 j l * f l = (C13 *ᵥ f) j := rfl
  rw [h, C13, SimpleGraph.adjMatrix_mulVec_apply, cycleGraph_neighborFinset,
    Finset.sum_pair hne]

