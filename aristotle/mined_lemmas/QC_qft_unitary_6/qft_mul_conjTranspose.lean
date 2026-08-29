/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Qft Unitary 6

The `N`-point quantum Fourier transform matrix
`F_N (j,k) = N^{-1/2} * ω^{j k}` with `ω = exp (2 π i / N)`
is unitary; specialized to `N = 2^6`, the 6-qubit QFT.
-/

namespace QC

open Complex Finset Matrix

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/

theorem qft_mul_conjTranspose {N : ℕ} (hN : N ≠ 0) :
    qftMatrix N * (qftMatrix N)ᴴ = 1 :=
  mul_eq_one_comm.mp (qft_conjTranspose_mul hN)

/-- The 6-qubit quantum Fourier transform matrix is unitary. -/
