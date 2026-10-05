/-
# Hadamard XZ
Category: Quantum Computing
Target: QC.hadamard_XZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QC

/-- The Pauli `X` gate (bit flip), as a complex `2 × 2` matrix. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` gate (phase flip), as a complex `2 × 2` matrix. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Hadamard gate `H = (1/√2) * !![1, 1; 1, -1]`. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • !![1, 1; 1, -1]

/-- `((√2 : ℝ) : ℂ) ≠ 0`. -/
theorem sqrtTwo_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  simp

/-- `((√2 : ℝ) : ℂ)⁻¹ ^ 2 = 1 / 2`. -/
theorem inv_sqrtTwo_sq : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ 2 = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hne := sqrtTwo_ne_zero
  field_simp
  linear_combination -h2

/--
**Hadamard, X and Z.**  The Hadamard gate is `(X + Z)/√2`, and it conjugates
`X` into `Z`, i.e. `H X H = Z`.
-/
theorem hadamard_XZ :
    hadamard = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (pauliX + pauliZ) ∧
      hadamard * pauliX * hadamard = pauliZ := by
  have hc := inv_sqrtTwo_sq
  constructor
  · unfold hadamard pauliX pauliZ
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · unfold hadamard pauliX pauliZ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf <;> rw [hc] <;> norm_num

end QC

