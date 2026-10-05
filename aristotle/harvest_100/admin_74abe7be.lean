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

/-- The primitive 8-th root of unity `exp (2 π i / 8)`. -/
noncomputable def omega8 : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8)

/-- The 3-qubit quantum Fourier transform matrix:
`(QFT₃) j k = ω^(j*k) / √8` with `ω = exp (2 π i / 8)`. -/
noncomputable def qft3 : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun j k => omega8 ^ (j.val * k.val) / (Real.sqrt 8 : ℝ)

lemma isPrimitiveRoot_omega8 : IsPrimitiveRoot omega8 8 := by
  have h := Complex.isPrimitiveRoot_exp 8 (by norm_num)
  simpa [omega8] using h

lemma omega8_pow_eight : omega8 ^ 8 = 1 := isPrimitiveRoot_omega8.pow_eq_one

lemma conj_omega8 : (starRingEnd ℂ) omega8 = omega8 ^ 7 := by
  have hinv : (starRingEnd ℂ) omega8 = omega8⁻¹ := by
    rw [omega8, ← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp [Complex.ext_iff]
  have h7 : omega8 ^ 7 * omega8 = 1 := by
    rw [← pow_succ]
    exact omega8_pow_eight
  rw [hinv]
  exact (eq_inv_of_mul_eq_one_left h7).symm

lemma sqrt_eight_sq : ((Real.sqrt 8 : ℝ) : ℂ) * ((Real.sqrt 8 : ℝ) : ℂ) = 8 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma geom_sum_eight (z : ℂ) (h8 : z ^ 8 = 1) (h1 : z ≠ 1) :
    ∑ l : Fin 8, z ^ (l : ℕ) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => z ^ i) 8, geom_sum_eq h1, h8, sub_self, zero_div]

lemma term_eq (j k l : Fin 8) :
    (star qft3) j l * qft3 l k = (omega8 ^ (7 * j.val + k.val)) ^ (l : ℕ) / 8 := by
  have hstar : (star qft3) j l = omega8 ^ (7 * (l.val * j.val)) / (Real.sqrt 8 : ℝ) := by
    rw [Matrix.star_apply]
    simp only [qft3, Matrix.of_apply, star_div', star_pow, Complex.star_def,
      Complex.conj_ofReal, conj_omega8, ← pow_mul]
    congr 1
    ring
  rw [hstar]
  simp only [qft3, Matrix.of_apply]
  rw [div_mul_div_comm, sqrt_eight_sq, ← pow_add, ← pow_mul]
  congr 2
  ring

theorem qft_unitary_3 : qft3 ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply]
  rw [Finset.sum_congr rfl (fun l _ => term_eq j k l), ← Finset.sum_div]
  have hz8 : (omega8 ^ (7 * j.val + k.val)) ^ 8 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, omega8_pow_eight, one_pow]
  by_cases h : j = k
  · subst h
    have hz : omega8 ^ (7 * j.val + j.val) = 1 := by
      have h8 : 7 * j.val + j.val = 8 * j.val := by ring
      rw [h8, pow_mul, omega8_pow_eight, one_pow]
    rw [hz]
    simp [Matrix.one_apply_eq]
  · have hz : omega8 ^ (7 * j.val + k.val) ≠ 1 := by
      rw [isPrimitiveRoot_omega8.pow_eq_one_iff_dvd]
      have hj := j.isLt
      have hk := k.isLt
      have hne : j.val ≠ k.val := fun hh => h (Fin.ext hh)
      omega
    rw [geom_sum_eight _ hz8 hz]
    simp [Matrix.one_apply_ne h]

end QC

