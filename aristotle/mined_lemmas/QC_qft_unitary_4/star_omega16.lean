import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix

/-- The primitive `16`-th root of unity `e^{2πi/16}` used by the 4-qubit QFT
(`N = 2^4 = 16`). -/

lemma star_omega16 : star omega16 = omega16⁻¹ := by
  show (starRingEnd ℂ) omega16 = _
  rw [omega16, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]
  ring

/-- For `k l : Fin 16`, the ratio `ω^k * (ω^l)⁻¹` is a 16-th root of unity. -/
