/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Polynomial SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of a
16-membered annulene, with `α = 0`, `β = 1`). -/

lemma scalar_mulVec (mu : ℂ) (v : Fin 16 → ℂ) : (Matrix.scalar (Fin 16) mu) *ᵥ v = mu • v := by
  rw [Matrix.scalar_apply]
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

