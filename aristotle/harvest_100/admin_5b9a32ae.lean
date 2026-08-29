-- /-!
-- # Qft Unitary 4
-- Category: Quantum Computing
-- Target: QC.qft_unitary_4
-- Verification: pending
-- Provenance: Aristotle theorem prover (Harmonic)
-- -/

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

open scoped Matrix

namespace QC

/-- The `N`-point discrete (quantum) Fourier transform matrix:
`(qftMatrix N) j k = N^(-1/2) * exp (2πi·jk/N)`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k =>
    ((Real.sqrt N : ℝ) : ℂ)⁻¹ *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) * (k : ℕ)) / N)

private lemma star_cexp (x : ℂ) : star (Complex.exp x) = Complex.exp (star x) := by
  simp [Complex.exp_conj]

/-- The `N`-th root of unity `exp (2πi·d/N)` differs from `1` when `N ∤ d`. -/
lemma root_ne_one {N : ℕ} (hN : 0 < N) {d : ℤ} (hd : ¬ ((N : ℤ) ∣ d)) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ)) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp at hn
  have hd' : (d : ℤ) = (N : ℤ) * n := by exact_mod_cast hn
  exact hd ⟨n, hd'⟩

/-- `exp (2πi·d/N)` is an `N`-th root of unity. -/
lemma root_pow_eq_one {N : ℕ} (hN : 0 < N) (d : ℤ) :
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ))) ^ N = 1 := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [← Complex.exp_nat_mul]
  have h2 : (N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ))
      = (d : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by field_simp
  rw [h2, Complex.exp_int_mul_two_pi_mul_I]

/-- The geometric sum of a nontrivial `N`-th root of unity vanishes. -/
lemma geom_sum_root_eq_zero {N : ℕ} (hN : 0 < N) {d : ℤ} (hd : ¬ ((N : ℤ) ∣ d)) :
    ∑ m ∈ Finset.range N,
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ))) ^ m = 0 := by
  rw [geom_sum_eq (root_ne_one hN hd), root_pow_eq_one hN d, sub_self, zero_div]

/-- Orthonormality of the QFT columns: `(qftMatrix N)ᴴ * (qftMatrix N) = 1`. -/
theorem qft_star_mul_self (N : ℕ) (hN : 0 < N) :
    star (qftMatrix N) * qftMatrix N = 1 := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hsq : ((Real.sqrt N : ℝ) : ℂ)⁻¹ * ((Real.sqrt N : ℝ) : ℂ)⁻¹ = (N : ℂ)⁻¹ := by
    rw [← mul_inv]
    congr 1
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    simp
  ext j k
  rw [Matrix.mul_apply]
  have hterm : ∀ m : Fin N,
      (star (qftMatrix N)) j m * qftMatrix N m k
        = (N : ℂ)⁻¹ *
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
            (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) / (N : ℂ))) ^ (m : ℕ) := by
    intro m
    rw [Matrix.star_apply]
    show star (qftMatrix N m j) * qftMatrix N m k = _
    simp only [qftMatrix, Matrix.of_apply]
    rw [star_mul', star_cexp, ← Complex.exp_nat_mul,
      show star ((((Real.sqrt N) : ℝ) : ℂ)⁻¹) = (((Real.sqrt N : ℝ)) : ℂ)⁻¹ by
        simp [← Complex.ofReal_inv],
      mul_mul_mul_comm, hsq, ← Complex.exp_add]
    congr 1
    rw [show star (2 * (Real.pi : ℂ) * Complex.I * ((m : ℕ) * (j : ℕ)) / N)
        = -(2 * (Real.pi : ℂ) * Complex.I * ((m : ℕ) * (j : ℕ)) / N) by
      simp [Complex.conj_I]; ring]
    push_cast
    field_simp
    ring_nf
  simp only [hterm]
  rw [← Finset.mul_sum]
  by_cases hjk : j = k
  · subst hjk
    simp only [sub_self, Int.cast_zero, mul_zero, zero_div, Complex.exp_zero, one_pow]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [Matrix.one_apply_eq, hNc]
  · have hd : ¬ ((N : ℤ) ∣ (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ))) := by
      intro hdvd
      have hj := j.isLt
      have hk := k.isLt
      have hlt : |(((k : ℕ) : ℤ) - ((j : ℕ) : ℤ))| < (N : ℤ) := by
        rw [abs_lt]; omega
      have h0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
      exact hjk (Fin.ext (by omega)).symm
    have hsum : ∑ m : Fin N,
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) / (N : ℂ))) ^ (m : ℕ) = 0 := by
      rw [Fin.sum_univ_eq_sum_range
        (fun m => (Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) / (N : ℂ))) ^ m) N]
      exact geom_sum_root_eq_zero hN hd
    rw [hsum, mul_zero, Matrix.one_apply_ne hjk]

/-- The 4-qubit quantum Fourier transform matrix, a `16 × 16` complex matrix. -/
noncomputable def qft4 : Matrix (Fin 16) (Fin 16) ℂ := qftMatrix 16

/-- **The 4-qubit QFT matrix is unitary.** -/
theorem qft_unitary_4 : qft4 ∈ Matrix.unitaryGroup (Fin 16) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  exact qft_star_mul_self 16 (by norm_num)

/-- Explicit form of unitarity: `qft4ᴴ * qft4 = 1`. -/
theorem qft4_conjTranspose_mul_self : qft4ᴴ * qft4 = 1 :=
  qft_star_mul_self 16 (by norm_num)

/-- Explicit form of unitarity: `qft4 * qft4ᴴ = 1`. -/
theorem qft4_mul_conjTranspose_self : qft4 * qft4ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp qft_unitary_4

end QC

