import Mathlib

/-!
# Hadamard Involutive
Category: Quantum Computing
Target: QC.hadamard_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix Complex

/-- The single-qubit Hadamard gate as a `2 × 2` complex matrix. -/

lemma inv_sq_ofReal_sqrt_two : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ^ 2 = 1 / 2 := by
  rw [inv_pow, sq_ofReal_sqrt_two]
  norm_num

/-- The Hadamard matrix is self-adjoint: `H† = H`. -/
