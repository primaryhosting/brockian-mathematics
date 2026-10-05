import Mathlib

/-!
# Hadamard XZ
Category: Quantum Computing
Target: QC.hadamard_XZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix Complex

/-- The Pauli `X` gate. -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` gate. -/
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Hadamard gate `H = (1/√2) * !![1, 1; 1, -1]`. -/
noncomputable def H : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • !![1, 1; 1, -1]

lemma sq_sqrt_two : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

lemma sqrt_two_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  simp

/-- `H = (X + Z)/√2` and `H * X * H = Z`. -/
theorem hadamard_XZ :
    H = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (X + Z) ∧ H * X * H = Z := by
  have h2 := sq_sqrt_two
  have hne := sqrt_two_ne_zero
  refine ⟨?_, ?_⟩
  · rw [H, X, Z]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [H, X, Z]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp <;>
      field_simp <;> linear_combination (2 : ℂ) * h2

end QC

