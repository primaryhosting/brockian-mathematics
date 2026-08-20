/-
# Hadamard Involutive
Category: Quantum Computing
Target: QC.hadamard_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix Complex

/-- The single-qubit Hadamard gate `H = (1/√2) • !![1, 1; 1, -1]`. -/

lemma sqrt_two_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  exact_mod_cast this.ne'

/-- The Hadamard gate is self-adjoint: `H† = H`. -/
