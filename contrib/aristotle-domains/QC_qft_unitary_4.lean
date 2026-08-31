/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Statement: The 4-qubit QFT matrix is unitary.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- The primitive `16`-th root of unity `exp(2πi/16)` used for the 4-qubit QFT. -/
noncomputable def omega16 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

/-- The 4-qubit quantum Fourier transform matrix: a `16 × 16` complex matrix with
entries `(1/√16) * ω^(j*k) = (1/4) * ω^(j*k)`, where `ω = exp(2πi/16)`. -/
noncomputable def qft4 : Matrix (Fin 16) (Fin 16) ℂ :=
  fun j k => (1 / 4 : ℂ) * omega16 ^ ((j : ℕ) * (k : ℕ))

lemma isPrimitiveRoot_omega16 : IsPrimitiveRoot omega16 16 := by
  have h := Complex.isPrimitiveRoot_exp 16 (by norm_num)
  simpa [omega16, mul_comm, mul_assoc, mul_left_comm] using h

lemma omega16_pow_16 : omega16 ^ (16 : ℕ) = 1 := isPrimitiveRoot_omega16.pow_eq_one

lemma omega16_ne_zero : omega16 ≠ 0 := by
  simp [omega16, Complex.exp_ne_zero]

lemma conj_omega16 : (starRingEnd ℂ) omega16 = omega16 ⁻¹ := by
  rw [omega16, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, map_ofNat, Complex.conj_ofReal]
  ring

/-- Geometric sum of a 16-th root of unity. -/
lemma sum_pow_eq (z : ℂ) (hz : z ^ (16 : ℕ) = 1) :
    ∑ i ∈ Finset.range 16, z ^ i = if z = 1 then (16 : ℂ) else 0 := by
  by_cases h : z = 1
  · simp [h]
  · rw [if_neg h, geom_sum_eq h, hz]
    simp

lemma omega16_pow_inj {j k : ℕ} (hj : j < 16) (hk : k < 16)
    (h : omega16 ^ j = omega16 ^ k) : j = k :=
  isPrimitiveRoot_omega16.pow_inj hj hk h

/-- **The 4-qubit QFT matrix is unitary.** -/
theorem qft_unitary_4 : qft4 ∈ Matrix.unitaryGroup (Fin 16) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply]
  have hstar : ∀ i : Fin 16, (star qft4) j i * qft4 i k
      = (1/16 : ℂ) * ((omega16 ^ (k : ℕ) * (omega16 ^ (j : ℕ))⁻¹) ^ (i : ℕ)) := by
    intro i
    have hs : (star qft4) j i = (starRingEnd ℂ) (qft4 i j) := rfl
    rw [hs, qft4, qft4]
    simp only [map_mul, map_pow, map_div₀, map_one, map_ofNat, conj_omega16]
    have e1 : (omega16⁻¹) ^ ((i : ℕ) * (j : ℕ)) = ((omega16 ^ (j : ℕ))⁻¹) ^ (i : ℕ) := by
      rw [mul_comm, pow_mul, inv_pow]
    have e2 : omega16 ^ ((i : ℕ) * (k : ℕ)) = (omega16 ^ (k : ℕ)) ^ (i : ℕ) := by
      rw [mul_comm, pow_mul]
    rw [e1, e2, mul_pow]
    ring
  simp only [hstar]
  rw [← Finset.mul_sum]
  set z : ℂ := omega16 ^ (k : ℕ) * (omega16 ^ (j : ℕ))⁻¹ with hzdef
  have hsum : ∑ i : Fin 16, z ^ (i : ℕ) = ∑ i ∈ Finset.range 16, z ^ i := by
    rw [Fin.sum_univ_eq_sum_range (fun i => z ^ i) 16]
  rw [hsum]
  have key : ∀ m : ℕ, (omega16 ^ m) ^ (16 : ℕ) = 1 := by
    intro m
    rw [← pow_mul, mul_comm, pow_mul, omega16_pow_16, one_pow]
  have hz16 : z ^ (16 : ℕ) = 1 := by
    rw [hzdef, mul_pow, key, inv_pow, key, inv_one, mul_one]
  rw [sum_pow_eq z hz16]
  have hzeq : z = 1 ↔ j = k := by
    constructor
    · intro h
      have hne : omega16 ^ (j : ℕ) ≠ 0 := pow_ne_zero _ omega16_ne_zero
      rw [hzdef, mul_inv_eq_one₀ hne] at h
      exact (Fin.ext (omega16_pow_inj k.isLt j.isLt h)).symm
    · intro h
      subst h
      rw [hzdef, mul_inv_cancel₀ (pow_ne_zero _ omega16_ne_zero)]
  by_cases h : j = k
  · rw [if_pos (hzeq.mpr h)]
    subst h
    simp
  · rw [if_neg (fun hc => h (hzeq.mp hc))]
    simp [h]

end QC

