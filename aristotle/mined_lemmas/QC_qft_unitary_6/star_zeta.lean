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

lemma star_zeta (N : ℕ) : star (zeta N) = (zeta N)⁻¹ := by
  show (starRingEnd ℂ) _ = _
  rw [zeta, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_div₀, Complex.conj_I, map_ofNat]
  ring

