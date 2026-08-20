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
