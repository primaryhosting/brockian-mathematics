import Mathlib

/-!
# Hadamard XZ
Category: Quantum Computing
Target: QC.hadamard_XZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix Complex

/-- The Pauli `X` gate. -/

lemma sqrt_two_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  simp

/-- `H = (X + Z)/√2` and `H * X * H = Z`. -/
