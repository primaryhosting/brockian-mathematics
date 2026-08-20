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

theorem qftMatrix_mem_unitaryGroup (N : ℕ) (hN : 0 < N) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / N)) N :=
    Complex.isPrimitiveRoot_exp N hN.ne'
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / N) with hζ
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have hstar : (starRingEnd ℂ) ζ = ζ⁻¹ := by
    rw [hζ, ← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp [map_div₀, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  have hNC : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hsq : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  rw [Matrix.mem_unitaryGroup_iff]
  ext i k
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply, qftMatrix, Matrix.one_apply, ← hζ]
  have hterm : ∀ x : Fin N, ζ ^ ((i : ℕ) * (x : ℕ)) / ((Real.sqrt N : ℝ) : ℂ) *
      star (ζ ^ ((k : ℕ) * (x : ℕ)) / ((Real.sqrt N : ℝ) : ℂ)) =
      (ζ ^ (i : ℕ) * (ζ ^ (k : ℕ))⁻¹) ^ (x : ℕ) / (N : ℂ) := by
    intro x
    rw [show (star (ζ ^ ((k : ℕ) * (x : ℕ)) / ((Real.sqrt N : ℝ) : ℂ))) =
        (ζ⁻¹) ^ ((k : ℕ) * (x : ℕ)) / ((Real.sqrt N : ℝ) : ℂ) by
      simp [hstar, Complex.conj_ofReal]]
    rw [mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, div_mul_div_comm, hsq]
  simp only [hterm]
  exact sum_pow_div_eq_ite hprim hζ0 hNC i k

/-- The 8-qubit QFT matrix is unitary. -/
