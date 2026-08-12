/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
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

/-- The `2^6 = 64`-dimensional quantum Fourier transform matrix:
`(QFT)_{j,k} = (1/8) * exp(2πi·jk/64)`, where `1/8 = 1/√64`. -/
noncomputable def qft6 : Matrix (Fin 64) (Fin 64) ℂ :=
  fun j k => (1 / 8 : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * I * ((j : ℕ) * (k : ℕ) : ℕ) / 64)

private lemma two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
  simp [Complex.I_ne_zero, Real.pi_ne_zero]

/-- The sum of the 64-th roots of unity `exp(2πi d/64)^k`, `k < 64`. -/
private lemma sum_geom_exp (d : ℤ) :
    ∑ k ∈ Finset.range 64, Complex.exp (2 * (Real.pi : ℂ) * I * (d : ℂ) / 64) ^ k
      = if (64 : ℤ) ∣ d then 64 else 0 := by
  by_cases hd : (64 : ℤ) ∣ d
  · obtain ⟨m, rfl⟩ := hd
    have h1 : Complex.exp (2 * (Real.pi : ℂ) * I * ((64 * m : ℤ) : ℂ) / 64) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨m, by push_cast; ring⟩
    rw [h1]
    simp
  · have hz1 : Complex.exp (2 * (Real.pi : ℂ) * I * (d : ℂ) / 64) ≠ 1 := by
      intro h
      rw [Complex.exp_eq_one_iff] at h
      obtain ⟨n, hn⟩ := h
      apply hd
      refine ⟨n, ?_⟩
      have hn' : (2 * (Real.pi : ℂ) * I) * ((d : ℂ) / 64)
          = (2 * (Real.pi : ℂ) * I) * (n : ℂ) := by linear_combination hn
      have h3 := mul_left_cancel₀ two_pi_I_ne_zero hn'
      field_simp at h3
      exact_mod_cast h3
    have hzn : Complex.exp (2 * (Real.pi : ℂ) * I * (d : ℂ) / 64) ^ 64 = 1 := by
      rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      exact ⟨d, by push_cast; ring⟩
    rw [geom_sum_eq hz1, hzn]
    simp [hd]

/-- Orthogonality of the rows of the QFT matrix. -/
private lemma sum_exp_fin (j l : Fin 64) :
    ∑ k : Fin 64, Complex.exp (2 * (Real.pi : ℂ) * I * (((j : ℤ) - (l : ℤ) : ℤ) : ℂ) * (k : ℕ) / 64)
      = if j = l then 64 else 0 := by
  have hrw : ∀ k : ℕ,
      Complex.exp (2 * (Real.pi : ℂ) * I * (((j : ℤ) - (l : ℤ) : ℤ) : ℂ) * (k : ℕ) / 64)
        = Complex.exp (2 * (Real.pi : ℂ) * I * (((j : ℤ) - (l : ℤ) : ℤ) : ℂ) / 64) ^ k := by
    intro k
    rw [← Complex.exp_nat_mul]
    ring_nf
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => Complex.exp (2 * (Real.pi : ℂ) * I *
      (((j : ℤ) - (l : ℤ) : ℤ) : ℂ) * (k : ℕ) / 64)) 64]
  simp only [hrw]
  rw [sum_geom_exp]
  have hiff : (64 : ℤ) ∣ ((j : ℤ) - (l : ℤ)) ↔ j = l := by
    constructor
    · intro h
      have hj : (j : ℕ) < 64 := j.isLt
      have hl : (l : ℕ) < 64 := l.isLt
      have : (j : ℕ) = (l : ℕ) := by omega
      exact Fin.ext this
    · rintro rfl
      simp
  simp [hiff]

/-- **The 6-qubit quantum Fourier transform matrix is unitary.** -/
theorem qft_unitary_6 : qft6 ∈ Matrix.unitaryGroup (Fin 64) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext j l
  rw [Matrix.mul_apply]
  have hstar : ∀ k : Fin 64, (star qft6) k l
      = (1 / 8 : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * I * ((l : ℕ) * (k : ℕ) : ℕ) / 64)) := by
    intro k
    show (starRingEnd ℂ) (qft6 l k) = _
    rw [qft6]
    rw [map_mul, ← Complex.exp_conj]
    have hc : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * I * (((l : ℕ) * (k : ℕ) : ℕ) : ℂ) / 64)
        = -(2 * (Real.pi : ℂ) * I * (((l : ℕ) * (k : ℕ) : ℕ) : ℂ) / 64) := by
      simp [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      ring
    rw [hc]
    simp [map_ofNat]
  have hprod : ∀ k : Fin 64, qft6 j k * (star qft6) k l
      = (1 / 64 : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * I * (((j : ℤ) - (l : ℤ) : ℤ) : ℂ) * (k : ℕ) / 64) := by
    intro k
    rw [hstar k, qft6]
    have harg : 2 * (Real.pi : ℂ) * I * (((j : ℕ) * (k : ℕ) : ℕ) : ℂ) / 64
        + -(2 * (Real.pi : ℂ) * I * (((l : ℕ) * (k : ℕ) : ℕ) : ℂ) / 64)
        = 2 * (Real.pi : ℂ) * I * (((j : ℤ) - (l : ℤ) : ℤ) : ℂ) * ((k : ℕ) : ℂ) / 64 := by
      push_cast
      ring
    rw [mul_mul_mul_comm, ← Complex.exp_add, harg]
    norm_num
  simp only [hprod]
  rw [← Finset.mul_sum, sum_exp_fin]
  by_cases h : j = l
  · subst h
    simp
  · simp [h]

/-- Explicit form of unitarity: `Uᴴ * U = 1` and `U * Uᴴ = 1`. -/
theorem qft6_conjTranspose_mul_self_and_self_mul :
    Matrix.conjTranspose qft6 * qft6 = 1 ∧ qft6 * Matrix.conjTranspose qft6 = 1 := by
  have h := qft_unitary_6
  exact ⟨Unitary.star_mul_self_of_mem h, Unitary.mul_star_self_of_mem h⟩

end QC

