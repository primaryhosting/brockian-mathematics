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

lemma diag_eq_cos (k : Fin n) :
    cyZeta n ^ (k : ℕ) + (cyZeta n ^ (k : ℕ))⁻¹
      = ((2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  have h : cyZeta n ^ (k : ℕ) = Complex.exp (2 * Real.pi * k / n * Complex.I) := by
    rw [cyZeta, ← Complex.exp_nat_mul]
    ring_nf
  rw [h, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos]
  ring_nf

/-- **Hückel spectrum of the cycle graph.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C n` (`n ≥ 3`) factors as `∏ k, (X - 2 cos (2πk/n))`; i.e. its
eigenvalues, with multiplicity, are the Hückel π-energies `2 cos (2πk/n)`, `k = 0, …, n-1`. -/
