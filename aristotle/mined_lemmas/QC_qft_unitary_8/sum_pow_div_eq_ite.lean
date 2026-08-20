/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The quantum Fourier transform on `n` qubits acts on the `2 ^ n`-dimensional state space.
Its matrix has entries `ω ^ (j * k) / √N` where `N = 2 ^ n` and `ω = exp (2 π i / N)`.

We define the QFT matrix for an arbitrary dimension `N`, prove it is unitary for every
`N > 0`, and specialize to `n = 8` qubits (`N = 256`).

Mathlib does not contain the QFT/DFT matrix as such; the key existing ingredients used are
`Complex.isPrimitiveRoot_exp`, `IsPrimitiveRoot.pow_inj`, and `geom_sum_eq`.
-/

namespace QC

open Complex Matrix

/-- The `N`-dimensional discrete Fourier transform (QFT) matrix:
`qftMatrix N j k = exp (2 π i / N) ^ (j * k) / √N`. -/

theorem sum_pow_div_eq_ite {N : ℕ} {ζ : ℂ} (hprim : IsPrimitiveRoot ζ N) (hζ0 : ζ ≠ 0)
    (hNC : (N : ℂ) ≠ 0) (i k : Fin N) :
    ∑ x : Fin N, (ζ ^ (i : ℕ) * (ζ ^ (k : ℕ))⁻¹) ^ (x : ℕ) / (N : ℂ) = if i = k then 1 else 0 := by
  set w : ℂ := ζ ^ (i : ℕ) * (ζ ^ (k : ℕ))⁻¹ with hw
  rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun x => w ^ x) N]
  by_cases h : i = k
  · subst h
    have hw' : w = 1 := by rw [hw]; field_simp
    simp [hw', hNC]
  · have hw1 : w ≠ 1 := by
      rw [hw]
      intro hc
      apply h
      have hpow : ζ ^ (i : ℕ) = ζ ^ (k : ℕ) := by
        field_simp at hc
        exact hc
      exact Fin.ext (hprim.pow_inj i.isLt k.isLt hpow)
    have hwN : w ^ N = 1 := by
      rw [hw, mul_pow, ← pow_mul, ← inv_pow, ← pow_mul, mul_comm (i : ℕ) N, mul_comm (k : ℕ) N,
        pow_mul, pow_mul, hprim.pow_eq_one]
      simp [hprim.pow_eq_one]
    rw [geom_sum_eq hw1, hwN]
    simp [h]

/-- The `N`-dimensional QFT matrix is unitary for every `N > 0`. -/
