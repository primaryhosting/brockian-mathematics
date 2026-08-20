import Mathlib

/-!
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset Matrix

/-- The primitive `n`-th root of unity `exp(2πi/n)` used in the quantum Fourier transform. -/

private lemma zeta_prim : IsPrimitiveRoot (qftOmega 64) 64 := by
  have := Complex.isPrimitiveRoot_exp 64 (by norm_num)
  simpa [qftOmega] using this

