/-
/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency (Hückel) matrix of the cycle graph `C n` is diagonalised by the discrete Fourier
matrix `U j k = ζ ^ (j * k)`, `ζ = exp (2πi/n)`; its eigenvalues are the Hückel π-energies
`2 cos (2πk/n)`, `k = 0, …, n-1`.
-/

namespace Chem

open Complex Polynomial Matrix Finset

variable {n : ℕ}

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma huckel_mul_cyDFT (hn : 3 ≤ n) :
    huckelMatrix n * cyDFT n =
      cyDFT n * diagonal (fun k : Fin n => cyZeta n ^ (k : ℕ) + (cyZeta n ^ (k : ℕ))⁻¹) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  ext j k
  rw [Matrix.mul_diagonal]
  have h1 : (huckelMatrix (m + 3) * cyDFT (m + 3)) j k
      = ∑ u ∈ (SimpleGraph.cycleGraph (m + 3)).neighborFinset j, cyDFT (m + 3) u k := by
    rw [huckelMatrix, Matrix.mul_apply]
    simpa [Matrix.mulVec, dotProduct] using
      (SimpleGraph.adjMatrix_mulVec_apply (α := ℂ) (G := SimpleGraph.cycleGraph (m + 3)) j
        fun u => cyDFT (m + 3) u k)
  have hne : (j - 1 : Fin (m + 3)) ≠ j + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc j, left_eq_add]
    exact ne_of_beq_false rfl
  rw [h1, SimpleGraph.cycleGraph_neighborFinset, Finset.sum_pair hne]
  set w : ℂ := cyZeta (m + 3) with hwdef
  set c : ℂ := w ^ (k : ℕ) with hc
  have hwn : w ^ (m + 3) = 1 := cyZeta_pow_n (by omega)
  have hcn : c ^ (m + 3) = 1 := by rw [hc, ← pow_mul, mul_comm, pow_mul, hwn, one_pow]
  have hc0 : c ≠ 0 := by rw [hc]; exact pow_ne_zero _ cyZeta_ne_zero
  have hval : ∀ u : Fin (m + 3), cyDFT (m + 3) u k = c ^ (u : ℕ) := by
    intro u; rw [hc, ← pow_mul, mul_comm (k : ℕ) (u : ℕ)]; rfl
  rw [hval, hval, hval]
  have hplus : c ^ ((j + 1 : Fin (m + 3)) : ℕ) = c ^ (j : ℕ) * c := pow_succ_fin c hcn j
  have hminus : c ^ ((j - 1 : Fin (m + 3)) : ℕ) = c ^ (j : ℕ) * c⁻¹ := by
    have h := pow_succ_fin c hcn (j - 1)
    rw [sub_add_cancel] at h
    rw [eq_mul_inv_iff_mul_eq₀ hc0]
    exact h.symm
  rw [hplus, hminus]
  ring

/-- The `k`-th eigenvalue `ζ^k + ζ^(-k)` is the Hückel π-energy `2 cos (2πk/n)`. -/
