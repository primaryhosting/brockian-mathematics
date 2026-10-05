import Mathlib

/-!
# Hadamard Involutive
Category: Quantum Computing
Target: QC.hadamard_involutive
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

set_option grind.warning false

namespace QC

open Matrix Complex

/-- The single-qubit Hadamard gate `H = (1/√2) • !![1, 1; 1, -1]` as a complex `2 × 2` matrix. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2)⁻¹ : ℝ) • !![1, 1; 1, -1]

/-- `(1/√2)` squared is `1/2`. -/
lemma inv_sqrt_two_sq : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
  rw [← Real.sqrt_inv, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
  norm_num

/-- The Hadamard gate is self-adjoint (Hermitian): `Hᴴ = H`. -/
theorem hadamard_conjTranspose : hadamardᴴ = hadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.conjTranspose_apply, Complex.conj_ofReal]

/-- The Hadamard gate is Hermitian. -/
theorem hadamard_isHermitian : hadamard.IsHermitian := hadamard_conjTranspose

/-- The Hadamard gate squares to the identity: `H * H = 1`. -/
theorem hadamard_mul_self : hadamard * hadamard = 1 := by
  have h2 : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ^ 2 = 1 / 2 := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, inv_sqrt_two_sq]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.mul_apply, Fin.sum_univ_succ, Complex.ofReal_inv] <;>
    ring_nf <;>
    rw [h2] <;>
    ring

/-- **Hadamard involutive**: the Hadamard matrix `H` is self-adjoint (`Hᴴ = H`)
and squares to the identity (`H² = I`). -/
theorem hadamard_involutive : hadamardᴴ = hadamard ∧ hadamard * hadamard = 1 :=
  ⟨hadamard_conjTranspose, hadamard_mul_self⟩

end QC

