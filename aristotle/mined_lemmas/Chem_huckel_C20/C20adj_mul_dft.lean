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

lemma C20adj_mul_dft :
    C20adj * C20dft = C20dft * Matrix.diagonal (fun k => ((C20eigenvalue k : ℝ) : ℂ)) := by
  ext i k
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  have h : ∑ j, C20adj i j * C20dft j k = (C20adj *ᵥ C20vec k) i := rfl
  rw [h, C20adj_mulVec_C20vec]
  simp [C20dft, mul_comm]

