/-
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex

namespace QC

/-- The primitive `2^7 = 128`-th root of unity `exp (2πi/128)`. -/

noncomputable def qft7 : Matrix (Fin 128) (Fin 128) ℂ :=
  Matrix.of fun j k => ((1 / Real.sqrt 128 : ℝ) : ℂ) * qftOmega ^ (j.val * k.val)

/-- Orthogonality relation for the `128`-th roots of unity. -/
