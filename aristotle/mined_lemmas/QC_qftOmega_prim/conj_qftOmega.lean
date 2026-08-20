/-
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex

namespace QC

/-- The primitive `2^7 = 128`-th root of unity `exp (2πi/128)`. -/

lemma conj_qftOmega : (starRingEnd ℂ) qftOmega = qftOmega⁻¹ := by
  rw [qftOmega, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

/-- The `7`-qubit quantum Fourier transform matrix, of size `2^7 = 128`:
`F j k = (1/√128) * exp(2πi j k / 128)`. -/
