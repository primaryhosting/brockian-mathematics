/-
# Hadamard XZ
Category: Quantum Computing
Target: QC.hadamard_XZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses a plain block comment because Lean 4 requires
-- `import` commands to precede any module docstring.)

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

/-- The Pauli `X` gate. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` gate. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Hadamard gate. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • !![1, 1; 1, -1]

/-- `√2 ≠ 0` as a complex number. -/
lemma sqrtTwo_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  have h : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  exact_mod_cast h.ne'

/-- `√2 * √2 = 2` as complex numbers. -/
lemma sqrtTwo_mul_self : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h

/-- **Hadamard from Paulis, and conjugation of `X`.**
The Hadamard gate equals `(X + Z)/√2`, and it conjugates `X` into `Z`. -/
theorem hadamard_XZ :
    hadamard = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (pauliX + pauliZ) ∧
      hadamard * pauliX * hadamard = pauliZ := by
  constructor
  · unfold hadamard pauliX pauliZ
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · unfold hadamard pauliX pauliZ
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hinv : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
      rw [← mul_inv, sqrtTwo_mul_self]
    rw [hinv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring_nf

end QC

