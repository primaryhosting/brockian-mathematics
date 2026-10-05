/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex Polynomial

namespace Chem

/-- A primitive 11-th root of unity. -/

theorem huckel_C11 :
    ((SimpleGraph.cycleGraph 11).adjMatrix ℂ).charpoly
      = ∏ k : Fin 11, (X - C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 11) : ℝ) : ℂ)) := by
  let U : (Matrix (Fin 11) (Fin 11) ℂ)ˣ :=
    ⟨dftMat, dftMatInv, dft_mul_inv, inv_mul_dft⟩
  have hUinv : (↑U⁻¹ : Matrix (Fin 11) (Fin 11) ℂ) = dftMatInv := rfl
  have hA : (SimpleGraph.cycleGraph 11).adjMatrix ℂ = dftMat * eigDiag * dftMatInv := by
    rw [← adj_mul_dft, mul_assoc, dft_mul_inv, mul_one]
  rw [hA]
  have := Matrix.charpoly_units_conj U eigDiag
  rw [hUinv] at this
  rw [show (↑U : Matrix (Fin 11) (Fin 11) ℂ) = dftMat from rfl] at this
  rw [this, eigDiag, Matrix.charpoly_diagonal]
  rfl

/-- The spectrum of the adjacency matrix of `C₁₁` is exactly
`{2 cos (2πk/11) : k = 0, …, 10}`. -/
