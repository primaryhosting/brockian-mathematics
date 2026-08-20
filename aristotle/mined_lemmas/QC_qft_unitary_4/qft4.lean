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

noncomputable def qft4 : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun j k => omega16 ^ ((j : ℕ) * (k : ℕ)) / 4

