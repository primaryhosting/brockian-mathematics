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

theorem sum_exp_eq_zero (N : ℕ) (hN : 0 < N) (d : ℤ) (hd : d ≠ 0) (hlt : d.natAbs < N) :
    ∑ m ∈ Finset.range N,
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ))) ^ m = 0 := by
  rw [geom_sum_eq (exp_two_pi_I_div_ne_one N hN d hd hlt), exp_two_pi_I_div_pow N hN d]
  simp

/-- The `N × N` QFT matrix is unitary (for `N > 0`). -/
