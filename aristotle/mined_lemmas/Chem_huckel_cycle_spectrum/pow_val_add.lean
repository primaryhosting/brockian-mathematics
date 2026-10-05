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

lemma pow_val_add {ζ : ℂ} (hζ : ζ ^ n = 1) (a b : Fin n) :
    ζ ^ ((a + b : Fin n)).val = ζ ^ a.val * ζ ^ b.val := by
  have h : ((a + b : Fin n)).val = (a.val + b.val) % n := rfl
  rw [h, pow_mod_eq hζ, pow_add]

/-- Euler's formula in the form `ω ^ k + (ω ^ k)⁻¹ = 2 cos (2 π k / n)`. -/
