/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real

namespace QC

open Complex Matrix Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

noncomputable def qftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k =>
    ((1 / Real.sqrt n : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / n)

