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
