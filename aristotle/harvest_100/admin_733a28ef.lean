import Mathlib

/-!
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-- The `N × N` quantum Fourier transform matrix:
`(QFT_N)_{j,k} = N^{-1/2} · exp(2πi·jk/N)`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k => (Real.sqrt N : ℂ)⁻¹ *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) * (k : ℕ) : ℕ) / (N : ℂ))

/-- A single product of entries appearing in `QFT · QFT*`. -/
theorem qftMatrix_mul_conj_entry (N : ℕ) (j k m : Fin N) :
    qftMatrix N j m * (starRingEnd ℂ) (qftMatrix N k m)
      = ((N : ℂ))⁻¹ *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((j : ℕ) : ℂ) - ((k : ℕ) : ℂ))
          * ((m : ℕ) : ℂ) / (N : ℂ)) := by
  have hN : 0 < N := Fin.pos j
  have hs : ((Real.sqrt N : ℂ))⁻¹ * ((Real.sqrt N : ℂ))⁻¹ = ((N : ℂ))⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    norm_num
  simp only [qftMatrix, Matrix.of_apply, map_mul, ← Complex.exp_conj]
  rw [show ((starRingEnd ℂ) ((Real.sqrt N : ℂ))⁻¹) = ((Real.sqrt N : ℂ))⁻¹ by
    simp [← Complex.ofReal_inv]]
  rw [mul_mul_mul_comm, hs, ← Complex.exp_add]
  congr 1
  have h2 : ((starRingEnd ℂ)
      (2 * (Real.pi : ℂ) * Complex.I * (((k : ℕ) * (m : ℕ) : ℕ) : ℂ) / (N : ℂ)))
      = -(2 * (Real.pi : ℂ) * Complex.I * (((k : ℕ) : ℂ) * ((m : ℕ) : ℂ)) / (N : ℂ)) := by
    push_cast
    simp [Complex.ext_iff]
    ring
  rw [h2]
  push_cast
  congr 1
  have h : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp
  ring

/-- If `d` is a nonzero integer of absolute value less than `N`, then `exp(2πi d/N) ≠ 1`. -/
theorem exp_two_pi_I_div_ne_one (N : ℕ) (hN : 0 < N) (d : ℤ) (hd : d ≠ 0)
    (hlt : d.natAbs < N) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ)) ≠ 1 := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  intro hcon
  rw [Complex.exp_eq_one_iff] at hcon
  obtain ⟨n, hn⟩ := hcon
  rw [div_eq_iff hNc] at hn
  have hdc : (d : ℂ) = (n : ℂ) * (N : ℂ) := by
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) * (d : ℂ)
        = (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * (N : ℂ)) := by linear_combination hn
    have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero, hpi]
    exact mul_left_cancel₀ hne h2
  have hdz : d = n * N := by exact_mod_cast hdc
  have hn0 : n ≠ 0 := by rintro rfl; simp at hdz; exact hd hdz
  have h1 : 1 ≤ |n| := Int.one_le_abs hn0
  have hle : (N : ℤ) ≤ |d| := by
    rw [hdz, abs_mul]
    calc (N : ℤ) = 1 * |(N : ℤ)| := by simp
    _ ≤ |n| * |(N : ℤ)| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  rw [Int.abs_eq_natAbs] at hle
  omega

/-- `exp(2πi d/N)` is an `N`-th root of unity. -/
theorem exp_two_pi_I_div_pow (N : ℕ) (hN : 0 < N) (d : ℤ) :
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ))) ^ N = 1 := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨d, ?_⟩
  field_simp

/-- Geometric sum of a nontrivial `N`-th root of unity vanishes. -/
theorem sum_exp_eq_zero (N : ℕ) (hN : 0 < N) (d : ℤ) (hd : d ≠ 0) (hlt : d.natAbs < N) :
    ∑ m ∈ Finset.range N,
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ))) ^ m = 0 := by
  rw [geom_sum_eq (exp_two_pi_I_div_ne_one N hN d hd hlt), exp_two_pi_I_div_pow N hN d]
  simp

/-- The `N × N` QFT matrix is unitary (for `N > 0`). -/
theorem qftMatrix_mul_conjTranspose (N : ℕ) (hN : 0 < N) :
    qftMatrix N * (qftMatrix N)ᴴ = 1 := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  ext j k
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Matrix.one_apply, Complex.star_def]
  have hterm : ∀ m : Fin N, qftMatrix N j m * (starRingEnd ℂ) (qftMatrix N k m)
      = ((N : ℂ))⁻¹ *
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I
          * ((((j : ℕ) : ℤ) - ((k : ℕ) : ℤ) : ℤ) : ℂ) / (N : ℂ))) ^ (m : ℕ) := by
    intro m
    rw [qftMatrix_mul_conj_entry N j k m]
    congr 1
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [Finset.sum_congr rfl (fun m _ => hterm m)]
  rw [← Finset.mul_sum]
  set d : ℤ := ((j : ℕ) : ℤ) - ((k : ℕ) : ℤ) with hd
  have hsum : (∑ m : Fin N,
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ))) ^ (m : ℕ))
      = ∑ m ∈ Finset.range N,
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ))) ^ m :=
    Fin.sum_univ_eq_sum_range
      (fun m => (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ))) ^ m) N
  rw [hsum]
  by_cases hjk : j = k
  · subst hjk
    have hd0 : d = 0 := by simp [hd]
    rw [hd0]
    simp [inv_mul_cancel₀ hNc]
  · have hd0 : d ≠ 0 := by
      simp only [hd, sub_ne_zero, ne_eq, Nat.cast_inj]
      exact fun h => hjk (Fin.ext h)
    have hlt : d.natAbs < N := by
      have hj := j.isLt
      have hk := k.isLt
      simp only [hd]
      omega
    rw [sum_exp_eq_zero N hN d hd0 hlt]
    simp [hjk]

/-- **The 5-qubit QFT matrix is unitary.** -/
theorem qft_unitary_5 : qftMatrix (2 ^ 5) ∈ Matrix.unitaryGroup (Fin (2 ^ 5)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  simpa [Matrix.star_eq_conjTranspose] using qftMatrix_mul_conjTranspose (2 ^ 5) (by norm_num)

end QC

