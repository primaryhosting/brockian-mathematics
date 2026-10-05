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
