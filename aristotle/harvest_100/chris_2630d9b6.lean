import Mathlib

/-!
# Hadamard XZ
Category: Quantum Computing
Target: QC.hadamard_XZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

/-- The Pauli `X` matrix. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` matrix. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Hadamard matrix `H = (1/√2) • !![1, 1; 1, -1]`. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ • !![1, 1; 1, -1]

/-- `(√2 : ℂ)^2 = 2`. -/
theorem sq_sqrt_two : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

/-- `(√2 : ℂ) ≠ 0`. -/
theorem sqrt_two_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := sq_sqrt_two
  rw [h] at this
  norm_num at this

/-- The Hadamard gate satisfies `H = (X + Z)/√2` and `H X H = Z`. -/
theorem hadamard_XZ :
    hadamard = (Real.sqrt 2 : ℂ)⁻¹ • (pauliX + pauliZ) ∧
      hadamard * pauliX * hadamard = pauliZ := by
  have h2 := sq_sqrt_two
  have hne := sqrt_two_ne_zero
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hadamard, pauliX, pauliZ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hadamard, pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      field_simp <;> ring_nf <;> rw [h2]

end QC

