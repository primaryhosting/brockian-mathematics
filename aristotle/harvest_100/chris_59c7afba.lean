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
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => (Complex.exp (2 * Real.pi * Complex.I / N)) ^ ((j : ℕ) * (k : ℕ)) / Real.sqrt N

/-- The QFT matrix on `n` qubits, acting on the `2 ^ n`-dimensional state space. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := qftMatrix (2 ^ n)

/-- Orthogonality of the rows of the QFT matrix: the geometric sum of the powers of
`ω ^ j * (ω ^ k)⁻¹` is `N` if `j = k` and `0` otherwise. -/
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
theorem qft_unitary_8 : qft 8 ∈ Matrix.unitaryGroup (Fin (2 ^ 8)) ℂ :=
  qftMatrix_mem_unitaryGroup (2 ^ 8) (by norm_num)

end QC

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

