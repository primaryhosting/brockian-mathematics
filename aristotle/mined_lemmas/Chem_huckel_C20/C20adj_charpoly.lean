/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex Matrix Polynomial

namespace Chem

/-- The adjacency matrix of the cycle graph `C₂₀`, with vertices indexed by `ZMod 20`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`.  In Hückel theory (with `α = 0`,
`β = 1`) this is the Hückel matrix of the annulene `C₂₀`. -/

theorem C20adj_charpoly :
    C20adj.charpoly = ∏ k : ZMod 20, (X - C ((C20eigenvalue k : ℝ) : ℂ)) := by
  have hconj : C20adj = (C20dftUnit : Matrix (ZMod 20) (ZMod 20) ℂ)
      * Matrix.diagonal (fun k => ((C20eigenvalue k : ℝ) : ℂ))
      * (↑C20dftUnit⁻¹ : Matrix (ZMod 20) (ZMod 20) ℂ) := by
    show C20adj = C20dft * Matrix.diagonal (fun k => ((C20eigenvalue k : ℝ) : ℂ))
      * ((20 : ℂ)⁻¹ • C20dftInv)
    rw [← C20adj_mul_dft, Matrix.mul_assoc, C20dft_mul_inv_one, mul_one]
  rw [hconj, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

/-- Conversely, every eigenvalue of the adjacency matrix of `C₂₀` is of the form
`2 cos (2πk/20)`. -/
