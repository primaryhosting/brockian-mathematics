/-
# Hadamard Involutive
Category: Quantum Computing
Target: QC.hadamard_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hadamard Involutive
Category: Quantum Computing
Target: QC.hadamard_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-- The single-qubit Hadamard gate, as the `2 × 2` complex matrix
`(1/√2) • !![1, 1; 1, -1]`. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2)⁻¹ : ℝ) • !![1, 1; 1, -1]

/-- The normalisation constant satisfies `(1/√2)² = 1/2` in `ℂ`. -/
lemma sqrt_two_inv_sq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ 2 = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  rw [inv_pow, h2]
  norm_num

/-- The Hadamard matrix is self-adjoint (Hermitian): `H† = H`. -/
theorem hadamard_conjTranspose : hadamard.conjTranspose = hadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hadamard, Matrix.conjTranspose_apply]

/-- The Hadamard matrix squares to the identity: `H² = I`. -/
theorem hadamard_sq : hadamard * hadamard = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    linear_combination (2 : ℂ) * sqrt_two_inv_sq

/-- **Hadamard is involutive**: the Hadamard gate is self-adjoint (`H† = H`) and
squares to the identity (`H² = I`). -/
theorem hadamard_involutive :
    hadamard.conjTranspose = hadamard ∧ hadamard * hadamard = 1 :=
  ⟨hadamard_conjTranspose, hadamard_sq⟩

end QC

