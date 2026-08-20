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

private lemma norm_zeta : ‖qftOmega 64‖ = 1 := zeta_prim.norm'_eq_one (by norm_num)

