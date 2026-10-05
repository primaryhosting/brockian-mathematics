import Mathlib
/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix

/-- The primitive `8`-th root of unity `ω = exp(2πi/8)` used by the 3-qubit QFT. -/

lemma conj_qftOmega : (starRingEnd ℂ) qftOmega = qftOmega ^ 7 := by
  have h1 : (starRingEnd ℂ) qftOmega = Complex.exp (-(2 * Real.pi * Complex.I / 8)) := by
    rw [qftOmega, ← Complex.exp_conj]
    congr 1
    simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  rw [h1, Complex.exp_neg, ← qftOmega]
  have hne : qftOmega ≠ 0 := Complex.exp_ne_zero _
  field_simp
  exact qftOmega_pow_eight.symm

/-- Orthogonality relation for the 8-th roots of unity. -/
