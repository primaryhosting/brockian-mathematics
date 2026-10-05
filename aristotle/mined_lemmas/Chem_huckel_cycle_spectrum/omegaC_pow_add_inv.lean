import Mathlib
/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
In Hückel molecular orbital theory the π-energies of an annulene `C_n H_n` are `α + β λ`,
where `λ` runs over the eigenvalues of the adjacency matrix of the cycle graph `C n`.
This file proves that this spectrum is exactly `{2 cos (2 π k / n) : k = 0, …, n-1}`.

The proof diagonalizes the (circulant) adjacency matrix by the Vandermonde/Fourier matrix
built from the `n`-th roots of unity.
-/

open scoped BigOperators Real

namespace Chem

open SimpleGraph Matrix Complex

/-- The Hückel (adjacency) matrix of the cycle graph `C n`, with entries in `ℂ`:
the `(i, j)` entry is `1` when `i` and `j` are adjacent in `C n`, and `0` otherwise. -/

lemma omegaC_pow_add_inv (hn : n ≠ 0) (k : ℕ) :
    (omegaC n) ^ k + ((omegaC n) ^ k)⁻¹
      = ((2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [omegaC, ← Complex.exp_nat_mul, ← Complex.exp_neg]
  push_cast
  rw [Complex.two_cos]
  congr 2 <;> field_simp

variable [NeZero n]

/-- Summing a function against the row of the adjacency matrix of `C n` picks out the two
neighbours `i - 1` and `i + 1`. -/
