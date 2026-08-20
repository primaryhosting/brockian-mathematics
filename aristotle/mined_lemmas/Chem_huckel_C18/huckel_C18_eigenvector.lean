/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Polynomial Finset

noncomputable section

/-- A primitive 18-th root of unity. -/

theorem huckel_C18_eigenvector (k : ZMod 18) :
    C18mat *ᵥ (fun j => wch (j * k)) = hval k • (fun j => wch (j * k)) := by
  funext j
  have key : (C18mat * Pmat) j k = (Pmat * Dmat) j k := by rw [C18mat_mul_Pmat]
  simp only [Matrix.mul_apply, Dmat, Pmat, Matrix.diagonal_apply] at key
  simpa [Matrix.mulVec, dotProduct, mul_comm] using key

/-- The Hückel eigenvectors are nonzero. -/
