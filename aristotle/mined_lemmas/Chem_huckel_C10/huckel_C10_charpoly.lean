/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix SimpleGraph Polynomial

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₁₀`.  This is the Hückel matrix of
cyclodecapentaene in units where the Coulomb integral `α` is `0` and the resonance integral
`β` is `1`. -/

theorem huckel_C10_charpoly :
    C10adj.charpoly = ∏ k : Fin 10, (X - C ((huckelEigenvalue k : ℝ) : ℂ)) := by
  obtain ⟨u, hu⟩ := dftU_isUnit
  set U : Matrix (Fin 10) (Fin 10) ℂ := (u : Matrix (Fin 10) (Fin 10) ℂ) with hU
  set Uinv : Matrix (Fin 10) (Fin 10) ℂ := ((u⁻¹ : (Matrix (Fin 10) (Fin 10) ℂ)ˣ) :
    Matrix (Fin 10) (Fin 10) ℂ) with hUinv
  have hconj : C10adj = U * C10diag * Uinv := by
    have h : C10adj * U = U * C10diag := by rw [hU, hu]; exact C10adj_mul_dftU
    calc C10adj = C10adj * (U * Uinv) := by rw [hU, hUinv, u.mul_inv, mul_one]
      _ = (C10adj * U) * Uinv := by rw [mul_assoc]
      _ = U * C10diag * Uinv := by rw [h]
  rw [hconj, Matrix.charpoly_units_conj, C10diag, Matrix.charpoly_diagonal]

/-- **Hückel theory for `C₁₀`.**  The eigenvalues (i.e. the spectrum) of the adjacency matrix of
the cycle graph `C₁₀` are exactly the numbers `2 cos (2πk/10)` for `k = 0, 1, …, 9`. -/
