/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Matrix Finset

/-- The primitive `64`-th root of unity `exp (2πi/64)` used by the 6-qubit QFT. -/
noncomputable def qftOmega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 64)

/-- The 6-qubit quantum Fourier transform matrix, of size `2^6 = 64`:
its `(j,k)` entry is `ω^(j*k) / √64 = ω^(j*k) / 8` with `ω = exp (2πi/64)`. -/
noncomputable def qftMatrix6 : Matrix (Fin 64) (Fin 64) ℂ :=
  fun j k => qftOmega ^ (j.val * k.val) / 8

theorem isPrimitiveRoot_qftOmega : IsPrimitiveRoot qftOmega 64 := by
  simpa [qftOmega] using Complex.isPrimitiveRoot_exp 64 (by norm_num)

theorem qftOmega_pow_64 : qftOmega ^ 64 = 1 := isPrimitiveRoot_qftOmega.pow_eq_one

theorem qftOmega_ne_zero : qftOmega ≠ 0 := Complex.exp_ne_zero _

theorem conj_qftOmega : (starRingEnd ℂ) qftOmega = qftOmega⁻¹ := by
  rw [qftOmega, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

/-- The orthogonality relation for the columns of the QFT matrix. -/
theorem qft_column_orthogonality (a b : Fin 64) :
    ∑ m : Fin 64, (qftOmega⁻¹) ^ (m.val * a.val) * qftOmega ^ (m.val * b.val)
      = if a = b then (64 : ℂ) else 0 := by
  set x : ℂ := (qftOmega⁻¹) ^ a.val * qftOmega ^ b.val with hx
  have hterm : ∀ m : Fin 64,
      (qftOmega⁻¹) ^ (m.val * a.val) * qftOmega ^ (m.val * b.val) = x ^ m.val := by
    intro m
    rw [hx, mul_pow, ← pow_mul, ← pow_mul, mul_comm a.val m.val, mul_comm b.val m.val]
  rw [Finset.sum_congr rfl fun m _ => hterm m, Fin.sum_univ_eq_sum_range (fun m => x ^ m) 64]
  by_cases hab : a = b
  · subst hab
    have : x = 1 := by
      rw [hx, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ qftOmega_ne_zero)]
    simp [this]
  · have hx1 : x ≠ 1 := by
      intro h
      apply hab
      rw [hx, inv_pow, inv_mul_eq_one₀ (pow_ne_zero _ qftOmega_ne_zero)] at h
      exact Fin.ext (isPrimitiveRoot_qftOmega.pow_inj a.isLt b.isLt h)
    have hx64 : x ^ 64 = 1 := by
      rw [hx, mul_pow, ← pow_mul, ← pow_mul, mul_comm a.val 64, mul_comm b.val 64,
        pow_mul, pow_mul, inv_pow, qftOmega_pow_64]
      simp
    rw [geom_sum_eq hx1, hx64, sub_self, zero_div, if_neg hab]

/-- The 6-qubit QFT matrix is unitary. -/
theorem qft_unitary_6 : qftMatrix6 ∈ Matrix.unitaryGroup (Fin 64) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  have hconj : ∀ n : ℕ, star (qftOmega ^ n / 8) = (qftOmega⁻¹) ^ n / 8 := by
    intro n
    show (starRingEnd ℂ) (qftOmega ^ n / 8) = _
    rw [map_div₀, map_pow, conj_qftOmega, map_ofNat, inv_pow]
  simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
    qftMatrix6, hconj, Matrix.one_apply]
  have hsplit : ∀ m : Fin 64,
      (qftOmega⁻¹) ^ (m.val * a.val) / 8 * (qftOmega ^ (m.val * b.val) / 8)
        = ((qftOmega⁻¹) ^ (m.val * a.val) * qftOmega ^ (m.val * b.val)) / 64 := by
    intro m; ring
  rw [Finset.sum_congr rfl fun m _ => hsplit m, ← Finset.sum_div, qft_column_orthogonality]
  split_ifs <;> norm_num

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

