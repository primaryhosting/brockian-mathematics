import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
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

set_option grind.warning false

namespace QC

/-- The primitive 16-th root of unity `exp (2πi/16)`. -/
noncomputable def zeta16 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

lemma zeta16_isPrimitiveRoot : IsPrimitiveRoot zeta16 16 := by
  simpa [zeta16] using Complex.isPrimitiveRoot_exp 16 (by norm_num)

lemma zeta16_pow_16 : zeta16 ^ (16 : ℕ) = 1 := zeta16_isPrimitiveRoot.pow_eq_one

lemma zeta16_ne_zero : zeta16 ≠ 0 := by
  intro h
  have := zeta16_pow_16
  rw [h] at this
  norm_num at this

lemma conj_ofNat_four : (starRingEnd ℂ) (4 : ℂ) = 4 := Complex.conj_eq_iff_re.mpr rfl

lemma conj_zeta16 : (starRingEnd ℂ) zeta16 = zeta16 ^ (15 : ℕ) := by
  have c2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_eq_iff_re.mpr rfl
  have c16 : (starRingEnd ℂ) (16 : ℂ) = 16 := Complex.conj_eq_iff_re.mpr rfl
  have hc : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I / 16)
      = -(2 * (Real.pi : ℂ) * Complex.I / 16) := by
    rw [map_div₀, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, c2, c16]
    ring
  have h1 : (starRingEnd ℂ) zeta16 = Complex.exp (-(2 * Real.pi * Complex.I / 16)) := by
    rw [zeta16, ← Complex.exp_conj, hc]
  have h2 : zeta16 * (starRingEnd ℂ) zeta16 = 1 := by
    rw [h1, zeta16, ← Complex.exp_add]
    simp
  have h3 : zeta16 * zeta16 ^ (15 : ℕ) = 1 := by
    rw [← pow_succ']
    exact zeta16_pow_16
  have := h2.trans h3.symm
  exact mul_left_cancel₀ zeta16_ne_zero this

/-- The 4-qubit quantum Fourier transform matrix, of size `16 × 16`. -/
noncomputable def qft4 : Matrix (Fin 16) (Fin 16) ℂ :=
  fun j k => zeta16 ^ (j.val * k.val) / 4

/-- Geometric sum of a 16-th root of unity over a full period. -/
lemma sum_pow_root (x : ℂ) (hx : x ^ (16 : ℕ) = 1) :
    ∑ k : Fin 16, x ^ (k : ℕ) = if x = 1 then 16 else 0 := by
  by_cases h : x = 1
  · simp [h]
  · rw [if_neg h, Fin.sum_univ_eq_sum_range (fun i => x ^ i) 16, geom_sum_eq h, hx]
    simp

theorem qft_unitary_4 : qft4 ∈ Matrix.unitaryGroup (Fin 16) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j l
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin 16,
      (star qft4) j k * qft4 k l
        = (zeta16 ^ (15 * j.val + l.val)) ^ (k : ℕ) / 16 := by
    intro k
    have hstar : (star qft4) j k = (starRingEnd ℂ) (zeta16 ^ (k.val * j.val) / 4) := by
      simp [qft4, conj_ofNat_four]
    have h4 : (starRingEnd ℂ) (4 : ℂ) = 4 := conj_ofNat_four
    rw [hstar, qft4]
    rw [map_div₀, map_pow, conj_zeta16, h4]
    rw [← pow_mul, ← pow_mul]
    rw [div_mul_div_comm, ← pow_add]
    have hidx : 15 * (k.val * j.val) + k.val * l.val = (15 * j.val + l.val) * k.val := by ring
    rw [hidx]
    norm_num
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.sum_div]
  rw [sum_pow_root _ (by rw [← pow_mul, mul_comm, pow_mul, zeta16_pow_16, one_pow])]
  by_cases hjl : j = l
  · subst hjl
    rw [if_pos (by
      have : (16 : ℕ) ∣ 15 * j.val + j.val := by
        have := j.isLt; omega
      exact zeta16_isPrimitiveRoot.pow_eq_one_iff_dvd _ |>.mpr this)]
    simp
  · rw [if_neg]
    · simp [hjl]
    · intro hcon
      have hdvd : (16 : ℕ) ∣ 15 * j.val + l.val :=
        (zeta16_isPrimitiveRoot.pow_eq_one_iff_dvd _).mp hcon
      have hj := j.isLt
      have hl := l.isLt
      exact hjl (Fin.ext (by omega))

/-- Entries of the 4-qubit QFT matrix: `(QFT)_{j k} = exp(2πi jk/16)/√16`. -/
lemma qft4_apply (j k : Fin 16) :
    qft4 j k = Complex.exp (2 * Real.pi * Complex.I * (j.val * k.val) / 16) / 4 := by
  rw [qft4, zeta16, ← Complex.exp_nat_mul]
  norm_num
  congr 1
  ring

/-- Explicit form of unitarity: `QFT^† * QFT = 1`. -/
theorem qft4_conjTranspose_mul_self : qft4.conjTranspose * qft4 = 1 :=
  (Matrix.mem_unitaryGroup_iff'.mp qft_unitary_4)

/-- Explicit form of unitarity: `QFT * QFT^† = 1`. -/
theorem qft4_mul_conjTranspose : qft4 * qft4.conjTranspose = 1 :=
  (Matrix.mem_unitaryGroup_iff.mp qft_unitary_4)

end QC

