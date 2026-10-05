/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat

set_option maxHeartbeats 1000000

namespace Chem

open SimpleGraph Matrix

/-- A primitive 15-th root of unity. -/

lemma adjMatrix_mul_apply (i k : Fin 15) :
    ((cycleGraph 15).adjMatrix ℂ * U) i k = U (i - 1) k + U (i + 1) k := by
  have hne : (i - 1 : Fin 15) ≠ i + 1 := by
    intro h
    have h2 : ((i - 1 : Fin 15) : ℕ) = ((i + 1 : Fin 15) : ℕ) := by rw [h]
    rw [fin15_sub_one_val, fin15_add_one_val] at h2
    omega
  have h1 : ((cycleGraph 15).adjMatrix ℂ * U) i k =
      ((cycleGraph 15).adjMatrix ℂ *ᵥ (fun j => U j k)) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h1, SimpleGraph.adjMatrix_mulVec_apply]
  have h2 : (cycleGraph 15).neighborFinset i = {i - 1, i + 1} :=
    @SimpleGraph.cycleGraph_neighborFinset 13 i
  rw [h2, Finset.sum_pair hne]

/-- The Fourier matrix diagonalizes the adjacency matrix of the 15-cycle. -/
