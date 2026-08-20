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

lemma pow_succ_fin [NeZero n] (z : ℂ) (hz : z ^ n = 1) (j : Fin n) :
    z ^ ((j + 1 : Fin n) : ℕ) = z ^ (j : ℕ) * z := by
  have hmod : ∀ a : ℕ, z ^ (a % n) = z ^ a := by
    intro a
    conv_rhs => rw [← Nat.div_add_mod a n]
    rw [pow_add, pow_mul, hz, one_pow, one_mul]
  have hv : ((j + 1 : Fin n) : ℕ) = ((j : ℕ) + 1) % n := by
    rw [Fin.val_add, Fin.val_one']
    conv_rhs => rw [Nat.add_mod]
    simp [Nat.add_mod]
  rw [hv, hmod, pow_succ]

/-- The Fourier matrix is invertible, with explicit inverse `cyDFTInv`. -/
