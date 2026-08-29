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

lemma inv_sqrt_sq {N : ℕ} :
    ((Real.sqrt N : ℝ) : ℂ)⁻¹ * ((Real.sqrt N : ℝ) : ℂ)⁻¹ = (N : ℂ)⁻¹ := by
  rw [← mul_inv]
  congr 1
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
  norm_cast

