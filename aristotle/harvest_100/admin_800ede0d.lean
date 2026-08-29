import Mathlib

/-!
# Hadamard Involutive
Category: Quantum Computing
Target: QC.hadamard_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix

/-- The single-qubit Hadamard gate `H = (1/√2) • !![1, 1; 1, -1]`, as a complex
`2 × 2` matrix. -/
noncomputable def hadamardMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / Real.sqrt 2 : ℝ) • !![1, 1; 1, -1]

/-- The Hadamard gate is self-adjoint: `Hᴴ = H`. -/
theorem hadamard_conjTranspose : hadamardMatrixᴴ = hadamardMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardMatrix, Matrix.conjTranspose_apply]

/-- The Hadamard gate squares to the identity: `H * H = 1`. -/
theorem hadamard_mul_self : hadamardMatrix * hadamardMatrix = 1 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [h2] <;> rw [h2] <;> norm_num

/-- **Hadamard involutive**: the Hadamard matrix satisfies `H† = H` and `H² = I`.
In particular it is a self-inverse (involutive) unitary. -/
theorem hadamard_involutive :
    hadamardMatrixᴴ = hadamardMatrix ∧ hadamardMatrix * hadamardMatrix = 1 :=
  ⟨hadamard_conjTranspose, hadamard_mul_self⟩

/-- Consequence: the Hadamard gate is unitary, `H† * H = 1`. -/
theorem hadamard_unitary : hadamardMatrixᴴ * hadamardMatrix = 1 := by
  rw [hadamard_conjTranspose, hadamard_mul_self]

end QC

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

