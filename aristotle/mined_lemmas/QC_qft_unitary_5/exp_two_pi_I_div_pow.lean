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

theorem exp_two_pi_I_div_pow (N : ℕ) (hN : 0 < N) (d : ℤ) :
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ))) ^ N = 1 := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨d, ?_⟩
  field_simp

/-- Geometric sum of a nontrivial `N`-th root of unity vanishes. -/
