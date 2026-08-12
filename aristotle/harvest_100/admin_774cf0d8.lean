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

/-- The single-qubit Hadamard gate `H = (1/√2) • !![1, 1; 1, -1]`
as a `2 × 2` complex matrix. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • !![1, 1; 1, -1]

/-- `(1/√2 : ℂ) * (1/√2) = 1/2`. -/
lemma inv_sqrt_two_sq : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    simp
  field_simp
  linear_combination -h

/-- The Hadamard gate is self-adjoint: `H† = H`. -/
theorem hadamard_conjTranspose : hadamard.conjTranspose = hadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.conjTranspose_apply]

/-- The Hadamard gate squares to the identity: `H * H = I`. -/
theorem hadamard_sq : hadamard * hadamard = 1 := by
  have key := inv_sqrt_two_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.mul_apply, Fin.sum_univ_succ, mul_comm] <;>
    linear_combination (2 : ℂ) * key

/-- **Hadamard involutive**: the Hadamard matrix `H` satisfies `H† = H` and `H² = I`. -/
theorem hadamard_involutive :
    hadamard.conjTranspose = hadamard ∧ hadamard * hadamard = 1 :=
  ⟨hadamard_conjTranspose, hadamard_sq⟩

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

