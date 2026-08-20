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

lemma C14adj_spectrum : spectrum ℂ C14adj = {μ | ∃ k : Fin 14, μ = C14eigval k} := by
  ext μ
  rw [spectrum.mem_iff]
  have halg : algebraMap ℂ (Matrix (Fin 14) (Fin 14) ℂ) μ = Matrix.scalar (Fin 14) μ := rfl
  rw [halg, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.eval_charpoly, C14adj_charpoly]
  simp only [Polynomial.eval_prod, eval_sub, eval_X, eval_C, Set.mem_setOf_eq]
  constructor
  · intro h
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h
    exact ⟨k, sub_eq_zero.1 hk⟩
  · rintro ⟨k, hk⟩
    exact Finset.prod_eq_zero (f := fun k => μ - C14eigval k) (Finset.mem_univ k)
      (by simp [hk])

