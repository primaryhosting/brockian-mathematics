/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The requested header is reproduced verbatim above; it is written as a plain block
-- comment rather than a `/-!` module docstring because Lean 4 does not allow a module
-- docstring to precede the `import` line.)

import Mathlib

namespace QC

open Complex Finset
open scoped Matrix

/-- The `n × n` quantum Fourier transform matrix: the entry in row `j`, column `k` is
`exp(2πi·j·k/n) / √n`. -/

noncomputable def qftRatio (n : ℕ) (j k : Fin n) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (((j : ℕ) : ℂ) - ((k : ℕ) : ℂ)) / n)

/-- Each term of the inner product of row `j` with row `k` is a power of `qftRatio`. -/
