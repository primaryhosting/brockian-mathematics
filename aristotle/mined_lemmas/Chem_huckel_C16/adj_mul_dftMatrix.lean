import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix SimpleGraph

/-- The Hückel (adjacency) matrix of the cycle graph `C₁₆`, over `ℝ`. -/

lemma adj_mul_dftMatrix :
    ((SimpleGraph.cycleGraph 16).adjMatrix ℂ) * dftMatrix
      = dftMatrix * Matrix.diagonal (fun k => (huckelEigenvalue k : ℂ)) := by
  ext i k
  have h1 : (((SimpleGraph.cycleGraph 16).adjMatrix ℂ) * dftMatrix) i k
      = (((SimpleGraph.cycleGraph 16).adjMatrix ℂ) *ᵥ (fun j => dftMatrix j k)) i := rfl
  rw [h1, SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (cycle_neighbors_ne i), Matrix.mul_diagonal, cycle_sub_one i]
  show w ^ (((i + 15 : Fin 16) : ℕ) * (k : ℕ)) + w ^ (((i + 1 : Fin 16) : ℕ) * (k : ℕ))
      = w ^ ((i : ℕ) * (k : ℕ)) * (huckelEigenvalue k : ℂ)
  rw [w_shift i 15 k, w_shift i 1 k, ← eigenvalue_eq k]
  show _ + _ = w ^ ((i : ℕ) * (k : ℕ)) * (w ^ (k : ℕ) + w ^ (15 * (k : ℕ)))
  have h15 : ((15 : Fin 16) : ℕ) = 15 := rfl
  have h11 : ((1 : Fin 16) : ℕ) = 1 := rfl
  rw [h15, h11, one_mul]
  ring

/-- The characteristic polynomial of the complex adjacency matrix of `C₁₆`. -/
