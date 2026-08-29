/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Qft Unitary 6

The `N`-point quantum Fourier transform matrix
`F_N (j,k) = N^{-1/2} * ω^{j k}` with `ω = exp (2 π i / N)`
is unitary; specialized to `N = 2^6`, the 6-qubit QFT.
-/

namespace QC

open Complex Finset Matrix

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/

theorem qft_conjTranspose_mul {N : ℕ} (hN : N ≠ 0) :
    (qftMatrix N)ᴴ * qftMatrix N = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin N, (qftMatrix N)ᴴ j k * qftMatrix N k l
      = (N : ℂ)⁻¹ * (star (zeta N ^ ((k : ℕ) * (j : ℕ))) * zeta N ^ ((k : ℕ) * (l : ℕ))) := by
    intro k
    simp only [Matrix.conjTranspose_apply, qftMatrix, Matrix.of_apply, star_mul',
      Complex.star_def, Complex.conj_ofReal, map_inv₀]
    rw [← inv_sqrt_sq]
    ring_nf
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum]
  have : ∑ k : Fin N, (star (zeta N ^ ((k : ℕ) * (j : ℕ))) * zeta N ^ ((k : ℕ) * (l : ℕ)))
      = ∑ k ∈ Finset.range N, (star (zeta N ^ (k * (j : ℕ))) * zeta N ^ (k * (l : ℕ))) :=
    Fin.sum_univ_eq_sum_range
      (fun k => star (zeta N ^ (k * (j : ℕ))) * zeta N ^ (k * (l : ℕ))) N
  rw [this, key_sum hN j l, Matrix.one_apply]
  by_cases h : j = l
  · simp [h, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN : (N : ℂ) ≠ 0)]
  · simp [h]

