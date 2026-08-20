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

lemma C14adj_mulVec_eigvec (k : Fin 14) :
    C14adj *ᵥ C14eigvec k = C14eigval k • C14eigvec k := by
  funext i
  have hv : ∀ j : Fin 14, C14eigvec k j = C14vand j k := fun j => by
    rw [C14vand_apply, C14eigvec]
  calc (C14adj *ᵥ C14eigvec k) i
      = ∑ j, C14adj i j * C14vand j k := by
        simp only [Matrix.mulVec, dotProduct, hv]
    _ = (C14adj * C14vand) i k := (Matrix.mul_apply).symm
    _ = (C14vand * Matrix.diagonal C14eigval) i k := by rw [C14adj_mul_vand]
    _ = C14vand i k * C14eigval k := by rw [Matrix.mul_diagonal]
    _ = (C14eigval k • C14eigvec k) i := by
        simp only [Pi.smul_apply, smul_eq_mul, hv i]; ring

