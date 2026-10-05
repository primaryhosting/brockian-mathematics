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
