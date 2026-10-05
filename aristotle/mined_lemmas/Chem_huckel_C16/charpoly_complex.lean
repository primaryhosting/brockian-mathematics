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

lemma charpoly_complex :
    ((SimpleGraph.cycleGraph 16).adjMatrix ℂ).charpoly
      = ∏ k : Fin 16, (X - C (huckelEigenvalue k : ℂ)) := by
  set u : (Matrix (Fin 16) (Fin 16) ℂ)ˣ :=
    ⟨dftMatrix, dftMatrixInv, dftMatrix_mul_dftMatrixInv, dftMatrixInv_mul_dftMatrix⟩ with hu
  have hconj : ((SimpleGraph.cycleGraph 16).adjMatrix ℂ)
      = (u : Matrix (Fin 16) (Fin 16) ℂ)
        * Matrix.diagonal (fun k => (huckelEigenvalue k : ℂ))
        * ((u⁻¹ : (Matrix (Fin 16) (Fin 16) ℂ)ˣ) : Matrix (Fin 16) (Fin 16) ℂ) := by
    have h := adj_mul_dftMatrix
    have : ((SimpleGraph.cycleGraph 16).adjMatrix ℂ) * dftMatrix * dftMatrixInv
        = dftMatrix * Matrix.diagonal (fun k => (huckelEigenvalue k : ℂ)) * dftMatrixInv := by
      rw [h]
    rwa [mul_assoc, dftMatrix_mul_dftMatrixInv, mul_one] at this
  rw [hconj, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

