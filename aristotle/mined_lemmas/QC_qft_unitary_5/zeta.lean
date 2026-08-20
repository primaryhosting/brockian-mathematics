/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix

/-- The primitive `N`-th root of unity `exp (2πi/N)`. -/

noncomputable def zeta (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / N)

/-- The `N × N` quantum Fourier transform matrix:
`(QFT_N)_{j,k} = (1/√N) · exp (2πi·j·k/N)`.
For `N = 2^n` this is the QFT acting on `n` qubits. -/
