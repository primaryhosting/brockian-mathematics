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

/-- The normalization constant `1/√2` of the Hadamard gate, as a complex number. -/
noncomputable def hc : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

/-- The single-qubit Hadamard gate `H = (1/√2) • !![1, 1; 1, -1]`. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  !![hc, hc; hc, -hc]

lemma hc_conj : (starRingEnd ℂ) hc = hc := by
  simp [hc, Complex.conj_ofReal]

lemma hc_sq : hc * hc = 1 / 2 := by
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  have : ((Real.sqrt 2)⁻¹ : ℝ) * ((Real.sqrt 2)⁻¹ : ℝ) = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt h2]
    norm_num
  simp only [hc, ← Complex.ofReal_mul, this]
  norm_num

/-- The Hadamard gate is Hermitian (self-adjoint). -/
theorem hadamard_conjTranspose : hadamardᴴ = hadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.conjTranspose_apply, hc_conj]

/-- The Hadamard gate is Hermitian, stated via `Matrix.IsHermitian`. -/
theorem hadamard_isHermitian : hadamard.IsHermitian := hadamard_conjTranspose

/-- The Hadamard gate squares to the identity. -/
theorem hadamard_sq : hadamard * hadamard = 1 := by
  have h := hc_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard] <;>
    ring_nf <;> linear_combination (2 : ℂ) * h

/-- **Hadamard involutive**: `H† = H` and `H² = I`. -/
theorem hadamard_involutive : hadamardᴴ = hadamard ∧ hadamard * hadamard = 1 :=
  ⟨hadamard_conjTranspose, hadamard_sq⟩

end QC

#print axioms QC.hadamard_involutive

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

