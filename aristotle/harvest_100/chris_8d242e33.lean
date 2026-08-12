/-
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QC

open Complex

/-- The primitive 8-th root of unity `exp(2πi/8)`. -/
noncomputable def omega8 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

/-- The 3-qubit quantum Fourier transform matrix, of size `8 × 8`, with entries
`ω^(j*k) / √8` where `ω = exp(2πi/8)`. -/
noncomputable def qft3 : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun j k => omega8 ^ ((j : ℕ) * (k : ℕ)) / (Real.sqrt 8 : ℝ)

lemma isPrimitiveRoot_omega8 : IsPrimitiveRoot omega8 8 := by
  simpa [omega8] using Complex.isPrimitiveRoot_exp 8 (by norm_num)

lemma omega8_pow_eight : omega8 ^ 8 = 1 := isPrimitiveRoot_omega8.pow_eq_one

lemma norm_omega8 : ‖omega8‖ = 1 := by
  simp [omega8, Complex.norm_exp]

lemma conj_omega8 : (starRingEnd ℂ) omega8 = omega8 ^ 7 := by
  have h : omega8 * omega8 ^ 7 = 1 := by
    rw [← pow_succ']
    exact omega8_pow_eight
  have hinv : omega8⁻¹ = (starRingEnd ℂ) omega8 := Complex.inv_eq_conj norm_omega8
  rw [← hinv]
  exact inv_eq_of_mul_eq_one_right h

/-- Sum of the 8-th roots of unity along an arithmetic progression of exponents. -/
lemma sum_omega8_pow (d : ℕ) :
    ∑ k ∈ Finset.range 8, (omega8 ^ d) ^ k = if 8 ∣ d then 8 else 0 := by
  by_cases hd : 8 ∣ d
  · have h1 : omega8 ^ d = 1 := (isPrimitiveRoot_omega8.pow_eq_one_iff_dvd d).2 hd
    simp [h1, hd]
  · have h1 : omega8 ^ d ≠ 1 := fun h =>
      hd ((isPrimitiveRoot_omega8.pow_eq_one_iff_dvd d).1 h)
    have h8 : (omega8 ^ d) ^ 8 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, omega8_pow_eight, one_pow]
    rw [geom_sum_eq h1 8, h8, if_neg hd]
    simp

lemma sqrt8_sq : ((Real.sqrt 8 : ℝ) : ℂ) * ((Real.sqrt 8 : ℝ) : ℂ) = 8 := by
  have : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this

/-- **The 3-qubit QFT matrix is unitary.** -/
theorem qft_unitary_3 : qft3 ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin 8,
      (star qft3) a k * qft3 k b = (omega8 ^ (7 * (a : ℕ) + (b : ℕ))) ^ (k : ℕ) / 8 := by
    intro k
    rw [Matrix.star_apply]
    show (starRingEnd ℂ) (qft3 k a) * qft3 k b = _
    simp only [qft3, Matrix.of_apply, map_div₀, map_pow, conj_omega8,
      Complex.conj_ofReal]
    rw [div_mul_div_comm, sqrt8_sq, ← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    ring
  simp only [key]
  rw [← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun k => (omega8 ^ (7 * (a : ℕ) + (b : ℕ))) ^ k) 8]
  rw [sum_omega8_pow]
  have ha := a.isLt
  have hb := b.isLt
  by_cases hab : a = b
  · subst hab
    have : (8 : ℕ) ∣ 7 * (a : ℕ) + (a : ℕ) := ⟨(a : ℕ), by ring⟩
    simp [this]
  · have hne : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
    have : ¬ (8 : ℕ) ∣ 7 * (a : ℕ) + (b : ℕ) := by omega
    simp [this, hab]

/-- The QFT matrix satisfies `Qᴴ * Q = 1`. -/
theorem qft3_conjTranspose_mul_self : qft3.conjTranspose * qft3 = 1 :=
  (Matrix.mem_unitaryGroup_iff'.1 qft_unitary_3)

/-- The QFT matrix satisfies `Q * Qᴴ = 1`. -/
theorem qft3_mul_conjTranspose_self : qft3 * qft3.conjTranspose = 1 :=
  (Matrix.mem_unitaryGroup_iff.1 qft_unitary_3)

#print axioms QC.qft_unitary_3

end QC

