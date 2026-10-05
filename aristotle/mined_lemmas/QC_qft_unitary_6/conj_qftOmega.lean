/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Matrix Finset

/-- The primitive `64`-th root of unity `exp (2πi/64)` used by the 6-qubit QFT. -/

theorem conj_qftOmega : (starRingEnd ℂ) qftOmega = qftOmega⁻¹ := by
  rw [qftOmega, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

/-- The orthogonality relation for the columns of the QFT matrix. -/
