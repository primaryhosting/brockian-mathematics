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

/-- The Pauli `X` matrix. -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` matrix. -/
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Hadamard matrix, `H = (X + Z) / √2`. -/
noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (X + Z)

lemma H_eq : H = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • !![1, 1; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H, X, Z]

/-- `H X H = Z`. -/
theorem hadamard_XZ : H * X * H = Z := by
  have hinv : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 2⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have key : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ) * X * !![1, 1; 1, -1]
      = (2 : ℂ) • Z := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [X, Z, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  rw [H_eq]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hinv, key, smul_smul]
  norm_num

#print axioms QC.hadamard_XZ

end QC

