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
