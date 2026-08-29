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

namespace QC

open Matrix

/-- The single-qubit Hadamard gate `H = (1/√2) • !![1, 1; 1, -1]`. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • !![1, 1; 1, -1]

lemma sq_inv_sqrt_two : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    have : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at h
    norm_num at h
  field_simp
  linear_combination -h

/-- The Hadamard matrix is self-adjoint and squares to the identity. -/
theorem hadamard_involutive :
    hadamard.conjTranspose = hadamard ∧ hadamard * hadamard = 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hadamard, Matrix.conjTranspose_apply, Matrix.smul_apply]
  · have h2 := sq_inv_sqrt_two
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hadamard, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      linear_combination (2 : ℂ) * h2

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

