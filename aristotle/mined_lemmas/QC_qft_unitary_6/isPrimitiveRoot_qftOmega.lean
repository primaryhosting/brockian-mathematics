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

theorem isPrimitiveRoot_qftOmega : IsPrimitiveRoot qftOmega 64 := by
  simpa [qftOmega] using Complex.isPrimitiveRoot_exp 64 (by norm_num)

