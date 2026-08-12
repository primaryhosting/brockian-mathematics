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

open Complex Finset

/-!
Mathlib (as of this version) contains no quantum-Fourier-transform matrix, so the matrix is
defined here.  The unitarity proof rests on the Mathlib lemmas
`Complex.isPrimitiveRoot_exp` (that `exp (2πI/N)` is a primitive `N`-th root of unity),
`geom_sum_eq` (closed form of a geometric sum) and `Matrix.mem_unitaryGroup_iff'`.
-/

namespace QC

/-- The `N × N` discrete Fourier transform (QFT) matrix:
`F i j = exp(2πi·jk/N) / √N`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (Real.sqrt N : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * (i.val * j.val) / N)

/-- The quantum Fourier transform on `n` qubits, a `2^n × 2^n` complex matrix. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := qftMatrix (2 ^ n)

/-- Geometric sum over an `N`-th root of unity distinct from `1` vanishes. -/
lemma sum_pow_eq_zero_of_ne_one {N : ℕ} {w : ℂ} (hw : w ^ N = 1) (hne : w ≠ 1) :
    ∑ j : Fin N, w ^ (j : ℕ) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => w ^ j) N, geom_sum_eq hne, hw, sub_self, zero_div]

/-- Entries of the QFT matrix as powers of the primitive root `exp(2πI/N)`. -/
lemma qftMatrix_apply (N : ℕ) (i j : Fin N) :
    qftMatrix N i j =
      (Real.sqrt N : ℂ)⁻¹ * (Complex.exp (2 * Real.pi * Complex.I / N)) ^ (i.val * j.val) := by
  rw [qftMatrix, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

lemma conj_exp_two_pi_I_div (N : ℕ) :
    (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I / N))
      = (Complex.exp (2 * Real.pi * Complex.I / N))⁻¹ := by
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_div₀, Complex.conj_I, map_ofNat]
  ring

theorem qftMatrix_unitary {N : ℕ} (hN : 0 < N) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I / N) with hzdef
  have hprim : IsPrimitiveRoot z N := Complex.isPrimitiveRoot_exp N hN.ne'
  have hzN : z ^ N = 1 := hprim.pow_eq_one
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hsqrt : ((Real.sqrt N : ℂ))⁻¹ * ((Real.sqrt N : ℂ))⁻¹ = (N : ℂ)⁻¹ := by
    have h : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = (N : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
      norm_cast
    rw [← mul_inv, h]
  rw [Matrix.mem_unitaryGroup_iff']
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have key : ∀ j : Fin N,
      (star (qftMatrix N)) i j * qftMatrix N j k
        = (N : ℂ)⁻¹ * ((z ^ i.val)⁻¹ * z ^ k.val) ^ j.val := by
    intro j
    rw [Matrix.star_apply, qftMatrix_apply, qftMatrix_apply]
    rw [star_mul', ← hzdef]
    have h1 : star ((Real.sqrt N : ℂ)⁻¹) = (Real.sqrt N : ℂ)⁻¹ := by
      simp [Complex.conj_ofReal]
    have h2 : star (z ^ (j.val * i.val)) = ((z ^ i.val)⁻¹) ^ j.val := by
      rw [Complex.star_def, map_pow, conj_exp_two_pi_I_div, ← hzdef, ← inv_pow, ← pow_mul,
        mul_comm j.val i.val, pow_mul]
    rw [h1, h2]
    have h3 : z ^ (j.val * k.val) = (z ^ k.val) ^ j.val := by
      rw [mul_comm, pow_mul]
    rw [h3, mul_pow]
    ring_nf
    rw [← hsqrt]
    ring
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]
  by_cases hik : i = k
  · subst hik
    rw [inv_mul_cancel₀ (pow_ne_zero i.val hz0), if_pos rfl]
    simp [inv_mul_cancel₀ hNC]
  · rw [if_neg hik]
    set w : ℂ := (z ^ i.val)⁻¹ * z ^ k.val with hw
    have hwN : w ^ N = 1 := by
      have h1 : (z ^ i.val) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hzN, one_pow]
      have h2 : (z ^ k.val) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hzN, one_pow]
      rw [hw, mul_pow, inv_pow, h1, h2, inv_one, one_mul]
    have hwne : w ≠ 1 := by
      intro h
      rw [hw, inv_mul_eq_one₀ (pow_ne_zero i.val hz0)] at h
      exact hik (Fin.ext (hprim.pow_inj i.isLt k.isLt h))
    rw [sum_pow_eq_zero_of_ne_one hwN hwne, mul_zero]

/-- **The `n`-qubit quantum Fourier transform matrix is unitary.** -/
theorem qft_unitary (n : ℕ) : qft n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rw [qft]
  exact qftMatrix_unitary (Nat.two_pow_pos n)

end QC

