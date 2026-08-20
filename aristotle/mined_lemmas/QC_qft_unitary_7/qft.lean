import Mathlib

/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset Matrix

/-- The `n × n` quantum Fourier transform matrix, with entries
`exp (2 π i j k / n) / √n`. -/

noncomputable def qft (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k =>
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) * (k : ℕ)) / n) / (Real.sqrt n : ℝ)

