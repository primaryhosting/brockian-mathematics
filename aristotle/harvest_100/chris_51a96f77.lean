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

namespace QC

/-- The (one-qubit) Hadamard matrix `H = (1/√2) • !![1, 1; 1, -1]` over `ℂ`. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2)⁻¹ : ℝ) • !![1, 1; 1, -1]

/-- `(1/√2)² = 1/2`, viewed in `ℂ`. -/
theorem inv_sqrt_two_sq : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ^ 2 = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [inv_pow, h]
  norm_num

/-- The Hadamard matrix is self-adjoint (`H† = H`) and involutive (`H² = I`). -/
theorem hadamard_involutive :
    hadamard.conjTranspose = hadamard ∧ hadamard * hadamard = 1 := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hadamard, Matrix.conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hadamard, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      ring_nf <;> rw [inv_sqrt_two_sq] <;> norm_num

end QC

