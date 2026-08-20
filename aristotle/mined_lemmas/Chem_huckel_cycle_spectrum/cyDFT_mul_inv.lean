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

lemma cyDFT_mul_inv (hn : n ≠ 0) : cyDFT n * cyDFTInv n = 1 := by
  have hprim := Complex.isPrimitiveRoot_exp n hn
  have hw : cyZeta n ^ n = 1 := hprim.pow_eq_one
  have hpow : ∀ a : ℕ, (cyZeta n ^ a) ^ n = 1 := by
    intro a; rw [← pow_mul, mul_comm, pow_mul, hw, one_pow]
  ext j l
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin n, cyDFT n j k * cyDFTInv n k l
      = (n : ℂ)⁻¹ * (cyZeta n ^ (j : ℕ) * (cyZeta n ^ (l : ℕ))⁻¹) ^ (k : ℕ) := by
    intro k
    simp only [cyDFT, cyDFTInv, mul_pow, inv_pow, ← pow_mul, mul_comm (k : ℕ) (l : ℕ)]
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum]
  set z : ℂ := cyZeta n ^ (j : ℕ) * (cyZeta n ^ (l : ℕ))⁻¹ with hz
  have hzn : z ^ n = 1 := by
    rw [hz, mul_pow, hpow, inv_pow, hpow, inv_one, one_mul]
  by_cases hjl : j = l
  · subst hjl
    have hz1 : z = 1 := by
      rw [hz]
      field_simp [pow_ne_zero _ (Complex.exp_ne_zero (2 * Real.pi * Complex.I / n)), cyZeta]
    rw [hz1]
    simp [Matrix.one_apply_eq, hn]
  · have hzne : z ≠ 1 := by
      rw [hz, ne_eq, mul_inv_eq_one₀ (pow_ne_zero _ (cyZeta_ne_zero (n := n)))]
      intro h
      exact hjl (Fin.ext (hprim.pow_inj j.isLt l.isLt h))
    have hsum : ∑ k : Fin n, z ^ (k : ℕ) = 0 := by
      rw [Fin.sum_univ_eq_sum_range fun k => z ^ k, geom_sum_eq hzne, hzn, sub_self, zero_div]
    rw [hsum, mul_zero, Matrix.one_apply_ne hjl]

/-- The Fourier matrix diagonalises the Hückel matrix of the cycle. -/
