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

lemma cyZeta_ne_zero : cyZeta n ≠ 0 := Complex.exp_ne_zero _

/-- Shifting the index by one in `Fin n` multiplies a power of an `n`-th root of unity by it. -/
