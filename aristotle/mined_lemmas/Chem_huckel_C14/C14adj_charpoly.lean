/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Polynomial SimpleGraph

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₄`. -/

lemma C14adj_charpoly :
    C14adj.charpoly = ∏ k : Fin 14, (X - C (C14eigval k)) := by
  obtain ⟨u, hu⟩ := C14vand_isUnit
  have hinv : (u⁻¹ : (Matrix (Fin 14) (Fin 14) ℂ)ˣ).val * C14adj * u.val
      = Matrix.diagonal C14eigval := by
    rw [mul_assoc, hu, C14adj_mul_vand, ← hu, ← mul_assoc]
    simp
  calc C14adj.charpoly
      = ((u⁻¹ : (Matrix (Fin 14) (Fin 14) ℂ)ˣ).val * C14adj * u.val).charpoly :=
        (Matrix.charpoly_units_conj' u C14adj).symm
    _ = (Matrix.diagonal C14eigval).charpoly := by rw [hinv]
    _ = ∏ k : Fin 14, (X - C (C14eigval k)) := Matrix.charpoly_diagonal _

