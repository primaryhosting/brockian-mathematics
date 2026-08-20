/-
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- A primitive `16`-th root of unity, `exp (2πi/16)`. -/

noncomputable def omega16 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

/-- The quantum Fourier transform matrix on 4 qubits: a `16 × 16` complex matrix with
entries `ω^(j k) / √16 = ω^(j k) / 4`, where `ω = exp (2πi/16)`. -/
