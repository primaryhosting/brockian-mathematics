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

/-
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/
noncomputable def zeta (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- The `N`-point discrete Fourier transform matrix, with entries
`exp (2 π i j k / N) / √N`. -/
noncomputable def dftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k =>
    Complex.exp (2 * Real.pi * Complex.I * (j.val * k.val) / N) / Real.sqrt N

/-- The quantum Fourier transform on `n` qubits: the `2 ^ n × 2 ^ n` DFT matrix,
with entries `exp (2 π i j k / 2 ^ n) / √(2 ^ n)`. -/
noncomputable def qftMatrix (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  dftMatrix (2 ^ n)

lemma zeta_isPrimitiveRoot {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (zeta N) N :=
  Complex.isPrimitiveRoot_exp N hN

lemma zeta_ne_zero (N : ℕ) : zeta N ≠ 0 := Complex.exp_ne_zero _

lemma dftMatrix_apply (N : ℕ) (j k : Fin N) :
    dftMatrix N j k = zeta N ^ (j.val * k.val) / Real.sqrt N := by
  unfold dftMatrix zeta
  simp only [Matrix.of_apply]
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- `exp (2 π i / N)` has modulus one, so conjugation inverts it. -/
lemma zeta_conj (N : ℕ) : (starRingEnd ℂ) (zeta N) = (zeta N)⁻¹ := by
  rw [Complex.inv_eq_conj]
  unfold zeta
  rw [Complex.norm_exp]
  simp

lemma zeta_zpow_pow {N : ℕ} (j l k : Fin N) :
    ((zeta N) ^ ((j.val : ℤ) - (l.val : ℤ))) ^ k.val
      = zeta N ^ (j.val * k.val) * (zeta N ^ (l.val * k.val))⁻¹ := by
  rw [← zpow_natCast (zeta N ^ _) k.val, ← zpow_mul, sub_mul, zpow_sub₀ (zeta_ne_zero N),
    div_eq_mul_inv]
  norm_cast

/-- The `(j, l)` term of the product `dftMatrix N * (dftMatrix N)ᴴ`. -/
lemma dft_mul_star_term {N : ℕ} (j l k : Fin N) :
    dftMatrix N j k * (star (dftMatrix N)) k l
      = ((zeta N) ^ ((j.val : ℤ) - (l.val : ℤ))) ^ k.val / (N : ℂ) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact absurd k.isLt (by omega)
  have hNR : (0:ℝ) < N := by positivity
  have hc : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hNR.le, Complex.ofReal_natCast]
  rw [Matrix.star_apply, dftMatrix_apply, dftMatrix_apply, zeta_zpow_pow, star_div₀, star_pow,
    Complex.star_def, zeta_conj, Complex.conj_ofReal, inv_pow, ← hc]
  field_simp

/-- Orthogonality relation: the geometric sum of the powers of `zeta N ^ (j - l)`
is `N` when `j = l` and `0` otherwise. -/
lemma sum_zeta_pow {N : ℕ} (hN : N ≠ 0) (j l : Fin N) :
    ∑ k ∈ Finset.range N, ((zeta N) ^ ((j.val : ℤ) - (l.val : ℤ))) ^ k
      = if j = l then (N : ℂ) else 0 := by
  have hprim := zeta_isPrimitiveRoot hN
  by_cases h : j = l
  · subst h; simp
  · have hne : (zeta N) ^ ((j.val : ℤ) - (l.val : ℤ)) ≠ 1 := by
      simp only [ne_eq, hprim.zpow_eq_one_iff_dvd]
      intro hdvd
      have h1 : (j.val : ℤ) - (l.val : ℤ) = 0 :=
        Int.eq_zero_of_abs_lt_dvd hdvd (by
          have hj := j.isLt
          have hl := l.isLt
          rw [abs_lt]; omega)
      exact h (Fin.ext (by omega))
    have hrN : ((zeta N) ^ ((j.val : ℤ) - (l.val : ℤ))) ^ N = 1 := by
      rw [← zpow_natCast (zeta N ^ _) N, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hprim.pow_eq_one, one_zpow]
    rw [geom_sum_eq hne, hrN, if_neg h]
    simp

/-- The `N`-point discrete Fourier transform matrix is unitary. -/
theorem dft_unitary {N : ℕ} (hN : N ≠ 0) : dftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext j l
  rw [Matrix.mul_apply]
  have hsum : ∑ k : Fin N, dftMatrix N j k * star (dftMatrix N) k l
      = (∑ k ∈ Finset.range N, ((zeta N) ^ ((j.val : ℤ) - (l.val : ℤ))) ^ k) / (N : ℂ) := by
    rw [Finset.sum_div,
      ← Fin.sum_univ_eq_sum_range
        (fun k => ((zeta N) ^ ((j.val : ℤ) - (l.val : ℤ))) ^ k / (N : ℂ)) N]
    exact Finset.sum_congr rfl fun k _ => dft_mul_star_term j l k
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [hsum, sum_zeta_pow hN]
  by_cases h : j = l <;> simp [h, Matrix.one_apply, hNC]

/-- The `n`-qubit quantum Fourier transform matrix is unitary. -/
theorem qft_unitary (n : ℕ) : qftMatrix n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  dft_unitary (by positivity)

end QC

