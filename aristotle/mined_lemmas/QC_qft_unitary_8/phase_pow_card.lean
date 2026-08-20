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

/-- The `N × N` Quantum Fourier Transform matrix:
`(QFT N) j k = exp (2 π i j k / N) / √N`. -/

private lemma phase_pow_card (hN : N ≠ 0) (a b : Fin N) : (phase N a b) ^ N = 1 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [phase, ← Complex.exp_nat_mul]
  rw [show (N : ℂ) * (2 * Real.pi * Complex.I * ((b : ℕ) - (a : ℕ)) / N)
        = (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) : ℤ) * (2 * Real.pi * Complex.I) by
    push_cast
    field_simp]
  exact Complex.exp_int_mul_two_pi_mul_I _

