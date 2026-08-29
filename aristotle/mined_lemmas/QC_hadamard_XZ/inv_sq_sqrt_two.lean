/-
# Hadamard XZ
Category: Quantum Computing
Target: QC.hadamard_XZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix

/-- The Pauli `X` gate. -/

lemma inv_sq_sqrt_two : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ^ 2 = 2⁻¹ := by
  rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, ← Real.sqrt_inv,
    Real.sq_sqrt (by norm_num : (2:ℝ)⁻¹ ≥ 0)]
  norm_num

/-- The Hadamard gate equals `(X + Z)/√2`. -/
