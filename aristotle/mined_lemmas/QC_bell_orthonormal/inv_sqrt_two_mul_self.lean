/-
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open scoped ComplexConjugate TensorProduct

/-- The two-qubit state space `ℂ² ⊗ ℂ²`, realized as the Hilbert space of functions on the
product index set `Fin 2 × Fin 2` (the computational basis `|ij⟩`).  The identification with
the algebraic tensor product `ℂ² ⊗[ℂ] ℂ²` is given by `QC.tensorEquiv` below. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- Coordinates of the four Bell states in the computational basis, before normalization. -/

lemma inv_sqrt_two_mul_self : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
  have h : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    have h' : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h'
  rw [← mul_inv, h]
  norm_num

/-! ## Orthonormality and completeness -/

/-- The Bell states form an orthonormal family. -/
