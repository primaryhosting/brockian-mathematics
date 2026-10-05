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
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 : ℂ) / (Real.sqrt 2 : ℂ)) • !![1, 1; 1, -1]

lemma sq_ofReal_sqrt_two : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma inv_sq_ofReal_sqrt_two : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ^ 2 = 1 / 2 := by
  rw [inv_pow, sq_ofReal_sqrt_two]
  norm_num

/-- The Hadamard matrix is self-adjoint: `H† = H`. -/
theorem hadamard_conjTranspose : hadamard.conjTranspose = hadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.conjTranspose_apply, Complex.conj_ofReal]

/-- The Hadamard matrix squares to the identity: `H² = I`. -/
theorem hadamard_sq : hadamard * hadamard = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;>
    rw [inv_sq_ofReal_sqrt_two] <;>
    norm_num

/-- The Hadamard gate is Hermitian and involutive: `H† = H` and `H² = I`. -/
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

