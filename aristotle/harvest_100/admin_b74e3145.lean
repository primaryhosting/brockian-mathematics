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
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 : ℂ) / (Real.sqrt 2 : ℝ)) • !![1, 1; 1, -1]

lemma sqrt_two_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  exact_mod_cast this.ne'

/-- The Hadamard gate is self-adjoint: `H† = H`. -/
theorem hadamard_conjTranspose : hadamard.conjTranspose = hadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.conjTranspose_apply]

/-- The Hadamard gate squares to the identity: `H * H = I`. -/
theorem hadamard_sq : hadamard * hadamard = 1 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num)
  have hne := sqrt_two_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;>
    first
      | linear_combination h2
      | linear_combination -h2

/-- The Hadamard matrix satisfies `H† = H` and `H² = I`. -/
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

