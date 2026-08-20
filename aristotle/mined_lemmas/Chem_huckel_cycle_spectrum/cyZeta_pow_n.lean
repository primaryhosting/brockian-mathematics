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

lemma cyZeta_pow_n (hn : n ≠ 0) : cyZeta n ^ n = 1 :=
  (Complex.isPrimitiveRoot_exp n hn).pow_eq_one

