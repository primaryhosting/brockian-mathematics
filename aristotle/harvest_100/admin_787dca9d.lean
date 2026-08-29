/-
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

/-- The primitive 8-th root of unity used by the 3-qubit QFT. -/
noncomputable def zeta8 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

/-- The 3-qubit quantum Fourier transform matrix, acting on the 8-dimensional state
space, with entries `(1/√8) * exp(2πi·jk/8)`. -/
noncomputable def qft3 : Matrix (Fin 8) (Fin 8) ℂ := fun j k =>
  (1 / Real.sqrt 8 : ℝ) * Complex.exp (2 * Real.pi * Complex.I * (j.val * k.val : ℕ) / 8)

lemma zeta8_isPrimitiveRoot : IsPrimitiveRoot zeta8 8 := by
  have := Complex.isPrimitiveRoot_exp 8 (by norm_num)
  simpa [zeta8] using this

lemma zeta8_pow_eight : zeta8 ^ 8 = 1 := zeta8_isPrimitiveRoot.pow_eq_one

lemma exp_eq_zeta8_pow (n : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (n : ℕ) / 8) = zeta8 ^ n := by
  rw [zeta8, ← Complex.exp_nat_mul]
  ring_nf

lemma sum_zeta8_pow (d : ℕ) :
    (∑ m : Fin 8, zeta8 ^ (m.val * d)) = if 8 ∣ d then 8 else 0 := by
  have hx : ∀ m : Fin 8, zeta8 ^ (m.val * d) = (zeta8 ^ d) ^ m.val := by
    intro m; rw [← pow_mul, Nat.mul_comm]
  simp only [hx]
  by_cases h : 8 ∣ d
  · obtain ⟨c, rfl⟩ := h
    have hone : zeta8 ^ (8 * c) = 1 := by
      rw [pow_mul, zeta8_pow_eight, one_pow]
    simp [hone]
  · have hne : zeta8 ^ d ≠ 1 := by
      intro hc
      exact h ((zeta8_isPrimitiveRoot.pow_eq_one_iff_dvd d).mp hc)
    have h8 : (zeta8 ^ d) ^ 8 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, zeta8_pow_eight, one_pow]
    have hgeom := geom_sum_eq hne 8
    rw [Fin.sum_univ_eq_sum_range (fun m => (zeta8 ^ d) ^ m) 8, hgeom, h8]
    simp [h]

lemma conj_zeta8 : (starRingEnd ℂ) zeta8 = zeta8 ^ 7 := by
  have h1 : zeta8 * (starRingEnd ℂ) zeta8 = 1 := by
    rw [zeta8, ← Complex.exp_conj, ← Complex.exp_add]
    have hz0 : (2 * (Real.pi : ℂ) * Complex.I / 8) +
        (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I / 8) = 0 := by
      simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      ring
    rw [hz0, Complex.exp_zero]
  have h2 : zeta8 * zeta8 ^ 7 = 1 := by
    calc zeta8 * zeta8 ^ 7 = zeta8 ^ 8 := by ring
      _ = 1 := zeta8_pow_eight
  have hz : zeta8 ≠ 0 := by
    intro hc
    rw [hc] at h2
    simp at h2
  exact mul_left_cancel₀ hz (h1.trans h2.symm)

/-- The 3-qubit QFT matrix is unitary. -/
theorem qft_unitary_3 : qft3 ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext j k
  rw [Matrix.mul_apply]
  have hentry : ∀ m : Fin 8, qft3 j m * (star qft3) m k
      = (1 / 8 : ℂ) * zeta8 ^ (m.val * (j.val + 7 * k.val)) := by
    intro m
    have hs : (star qft3) m k = (starRingEnd ℂ) (qft3 k m) := rfl
    rw [hs, qft3, qft3, exp_eq_zeta8_pow, exp_eq_zeta8_pow]
    have hsq : ((1 / Real.sqrt 8 : ℝ) : ℂ) * ((1 / Real.sqrt 8 : ℝ) : ℂ) = (1 / 8 : ℂ) := by
      have h8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
      have : (1 / Real.sqrt 8 : ℝ) * (1 / Real.sqrt 8 : ℝ) = 1 / 8 := by
        field_simp
        linarith [h8]
      rw [← Complex.ofReal_mul, this]
      norm_num
    rw [map_mul, Complex.conj_ofReal, map_pow, conj_zeta8, ← pow_mul]
    calc ((1 / Real.sqrt 8 : ℝ) : ℂ) * zeta8 ^ (j.val * m.val) *
          (((1 / Real.sqrt 8 : ℝ) : ℂ) * zeta8 ^ (7 * (k.val * m.val)))
        = (((1 / Real.sqrt 8 : ℝ) : ℂ) * ((1 / Real.sqrt 8 : ℝ) : ℂ)) *
            (zeta8 ^ (j.val * m.val) * zeta8 ^ (7 * (k.val * m.val))) := by ring
      _ = (1 / 8 : ℂ) * zeta8 ^ (m.val * (j.val + 7 * k.val)) := by
            rw [hsq, ← pow_add]; ring_nf
  simp only [hentry, ← Finset.mul_sum, sum_zeta8_pow]
  have hj := j.isLt
  have hk := k.isLt
  have hdvd : (8 ∣ (j.val + 7 * k.val)) ↔ j = k := by
    rw [Fin.ext_iff]
    omega
  rw [Matrix.one_apply]
  by_cases hjk : j = k
  · rw [if_pos (hdvd.mpr hjk), if_pos hjk]
    norm_num
  · rw [if_neg (fun hc => hjk (hdvd.mp hc)), if_neg hjk]
    norm_num

/-- Explicit form of unitarity: `qft3ᴴ * qft3 = 1`. -/
theorem qft3_conjTranspose_mul_self : Matrix.conjTranspose qft3 * qft3 = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp qft_unitary_3

/-- Explicit form of unitarity: `qft3 * qft3ᴴ = 1`. -/
theorem qft3_mul_conjTranspose_self : qft3 * Matrix.conjTranspose qft3 = 1 :=
  Matrix.mem_unitaryGroup_iff.mp qft_unitary_3

#print axioms qft_unitary_3

end QC

