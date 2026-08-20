/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency eigenvalues of the cycle graph `C n` (for `n ≥ 3`) are exactly
`2 cos (2πk/n)`, `k = 0, …, n-1`; these are the Hückel π-electron energies
(in units of the resonance integral `β`, measured from the Coulomb integral `α`).

The proof diagonalises the adjacency matrix by the discrete Fourier matrix
`F j k = ζ^(jk)` with `ζ = exp(2πi/n)`, and then uses `spectrum_diagonal`
(Mathlib, `Mathlib/LinearAlgebra/Eigenspace/Matrix.lean`) together with
`spectrum.units_conjugate`.
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- The primitive `n`-th root of unity `exp(2πi/n)`. -/

lemma adjMatrix_mul_fourier {n : ℕ} (hn : 3 ≤ n) :
    (cycleGraph n).adjMatrix ℂ * fourier n
      = fourier n * Matrix.diagonal
        (fun k : Fin n => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / n) : ℝ) : ℂ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 1 ≤ m := by omega
  have hn0 : m + 2 ≠ 0 := by omega
  ext j l
  rw [SimpleGraph.adjMatrix_mul_apply, Matrix.mul_diagonal, cycleGraph_neighborFinset]
  have hne : (j - 1 : Fin (m + 2)) ≠ j + 1 := by
    intro h
    have h1 : j = j + 1 + 1 := sub_eq_iff_eq_add.mp h
    rw [add_assoc] at h1
    have h2 : ((1 : Fin (m + 2)) + 1) = 0 := by simpa using h1.symm
    have h3 : ((1 : Fin (m + 2)) + 1).val = 2 % (m + 2) := by
      rw [Fin.val_add]
      norm_num [Fin.val_one]
    rw [h2, Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at h3
    exact absurd h3 (by norm_num)
  rw [Finset.sum_pair hne]
  simp only [fourier, Matrix.of_apply]
  have hsucc : ((j + 1 : Fin (m + 2)) : ℕ) = ((j : ℕ) + 1) % (m + 2) := by
    simp [Fin.val_add]
  have hpred : ((j - 1 : Fin (m + 2)) : ℕ) = ((j : ℕ) + (m + 1)) % (m + 2) := by
    rw [Fin.sub_def]
    simp only [Fin.val_one]
    congr 1
    omega
  have e1 : zeta (m + 2) ^ (((j + 1 : Fin (m + 2)) : ℕ) * (l : ℕ))
      = zeta (m + 2) ^ ((j : ℕ) * (l : ℕ)) * zeta (m + 2) ^ (l : ℕ) := by
    rw [hsucc]
    calc zeta (m + 2) ^ ((((j : ℕ) + 1) % (m + 2)) * (l : ℕ))
        = zeta (m + 2) ^ (((((j : ℕ) + 1) % (m + 2)) * (l : ℕ)) % (m + 2)) := by
          rw [zeta_pow_mod hn0]
      _ = zeta (m + 2) ^ (((((j : ℕ) + 1)) * (l : ℕ)) % (m + 2)) := by
          rw [Nat.mod_mul_mod]
      _ = zeta (m + 2) ^ ((((j : ℕ) + 1)) * (l : ℕ)) := zeta_pow_mod hn0 _
      _ = zeta (m + 2) ^ ((j : ℕ) * (l : ℕ)) * zeta (m + 2) ^ (l : ℕ) := by
          rw [← pow_add]; ring_nf
  have e2 : zeta (m + 2) ^ (((j - 1 : Fin (m + 2)) : ℕ) * (l : ℕ))
      = zeta (m + 2) ^ ((j : ℕ) * (l : ℕ)) * zeta (m + 2) ^ ((m + 1) * (l : ℕ)) := by
    rw [hpred]
    calc zeta (m + 2) ^ ((((j : ℕ) + (m + 1)) % (m + 2)) * (l : ℕ))
        = zeta (m + 2) ^ (((((j : ℕ) + (m + 1)) % (m + 2)) * (l : ℕ)) % (m + 2)) := by
          rw [zeta_pow_mod hn0]
      _ = zeta (m + 2) ^ ((((j : ℕ) + (m + 1)) * (l : ℕ)) % (m + 2)) := by
          rw [Nat.mod_mul_mod]
      _ = zeta (m + 2) ^ (((j : ℕ) + (m + 1)) * (l : ℕ)) := zeta_pow_mod hn0 _
      _ = zeta (m + 2) ^ ((j : ℕ) * (l : ℕ)) * zeta (m + 2) ^ ((m + 1) * (l : ℕ)) := by
          rw [← pow_add]; ring_nf
  rw [e1, e2, two_cos_eq hn0 l]
  have hm1 : (m + 2 - 1) = m + 1 := by omega
  rw [hm1]
  ring

/-- **Hückel spectrum of the cycle graph.**
For `n ≥ 3`, the spectrum of the adjacency matrix of the cycle graph `C n` is exactly the set
`{2 cos (2πk/n) : k = 0, …, n-1}`. These are the Hückel π-orbital energies (in units of the
resonance integral `β`, relative to the Coulomb integral `α`). -/
