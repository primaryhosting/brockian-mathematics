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

lemma two_cos_eq {n : ℕ} (hn : n ≠ 0) (l : Fin n) :
    ((2 * Real.cos (2 * Real.pi * (l : ℕ) / n) : ℝ) : ℂ)
      = zeta n ^ (l : ℕ) + zeta n ^ ((n - 1) * (l : ℕ)) := by
  have ha : zeta n ^ (l : ℕ) ≠ 0 := pow_ne_zero _ (zeta_ne_zero n)
  have hpow : zeta n ^ ((n - 1) * (l : ℕ)) = (zeta n ^ (l : ℕ))⁻¹ := by
    have hsum : zeta n ^ (l : ℕ) * zeta n ^ ((n - 1) * (l : ℕ)) = 1 := by
      rw [← pow_add]
      have he : (l : ℕ) + (n - 1) * (l : ℕ) = n * (l : ℕ) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
      rw [he, pow_mul, zeta_pow_self hn, one_pow]
    field_simp
    linear_combination hsum
  rw [hpow]
  have hz : zeta n ^ (l : ℕ) = Complex.exp (((2 * Real.pi * (l : ℕ) / n : ℝ) : ℂ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hz, ← Complex.exp_neg, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-- The adjacency matrix of the cycle graph is diagonalised by the Fourier matrix. -/
