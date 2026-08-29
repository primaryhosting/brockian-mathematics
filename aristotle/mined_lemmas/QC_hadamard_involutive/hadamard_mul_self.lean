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
