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

lemma fourier_mul_fourierInv {n : ℕ} (hn : n ≠ 0) : fourier n * fourierInv n = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have hsplit : ∀ k : Fin n, fourier n j k * fourierInv n k l
      = (n : ℂ)⁻¹ * (zeta n ^ ((j : ℕ) * (k : ℕ)) * (zeta n)⁻¹ ^ ((k : ℕ) * (l : ℕ))) := by
    intro k; simp only [fourier, fourierInv, Matrix.of_apply]; ring
  rw [Finset.sum_congr rfl fun k _ => hsplit k, ← Finset.mul_sum, sum_zeta_pow hn]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  by_cases hjl : j = l <;> simp [hjl, Matrix.one_apply, hn']

/-- The `l`-th Hückel energy written as a sum of two roots of unity. -/
