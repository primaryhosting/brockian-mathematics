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

namespace QC

open Complex Finset

/-- The `n`-qubit quantum Fourier transform matrix, of size `2 ^ n × 2 ^ n`:
`(QFT)_{j,k} = (1 / √(2^n)) * exp (2 π i j k / 2^n)`. -/

lemma exp_pow_eq_one {N : ℕ} (hN : 0 < N) (d : ℤ) :
    (Complex.exp (2 * Real.pi * Complex.I * (d : ℂ) / (N : ℂ))) ^ N = 1 := by
  have hNc : (N : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr hN.ne'
  rw [← Complex.exp_nat_mul]
  have : (N : ℂ) * (2 * Real.pi * Complex.I * (d : ℂ) / (N : ℂ))
      = (d : ℂ) * (2 * Real.pi * Complex.I) := by
    field_simp
  rw [this, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]

/-- Orthogonality of the QFT rows: the key exponential-sum identity. -/
